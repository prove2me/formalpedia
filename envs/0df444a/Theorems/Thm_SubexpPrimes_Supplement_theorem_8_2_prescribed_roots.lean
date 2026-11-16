-- Prove2me | Theorems.Thm_SubexpPrimes_Supplement_theorem_8_2_prescribed_roots
-- name    : SubexpPrimes.Supplement.theorem_8_2_prescribed_roots
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:48:37.91935+00:00
-- url     : https://prove2.me/theorems/69568efe-057a-494d-825e-1fbd297a5308
-- title:
--   Theorem 8.2 — least constrained prime with a prescribed number of roots of $f$ modulo $p$
-- statement:
--   Fix $d\ge1$. Let $C$ be an **admissible** constraint (Definition 2.3) on $n$-bit strings with description of length $L$, let $f\in\mathbb Z[X]$ be monic of degree $d$ with coefficients of $O(n)$ bits, and let $r_0\in\{0,\dots,d\}$. For a prime $p$ let $r_p$ be the number of $u\in\mathbb Z/p\mathbb Z$ with $f(u)\equiv0\pmod p$. Then a single deterministic machine decides whether some prime $p<2^n$ with $C(p)=1$ has $r_p=r_0$, and if so outputs the least one, in time
--
--   $$
--   \mathrm{poly}(n+L)\,2^{O_d(n/\sqrt{\log n})}
--   $$
--
--   and polynomial space. In particular, for a monic cubic $f$ one can find the least prime $p<2^n$ satisfying $C$ modulo which $f$ is irreducible, or decide that there is none, within the same bounds.
--
--   The constraint may encode a short interval or prescribed digits, where no density theorem guarantees such a prime.
--
--   **Formalization Note** "$O(n)$ bits" means: for a constant $c$ fixed together with $d$, every coefficient has absolute value below $2^{c(n+1)}$. The machine and its constant depend on $d$, $c$ and the admissible family. Time is $K(n+L+1)^K2^{Kn/\sqrt{\log_2 n}}$ and space $K(n+L+1)^K$.
--
--   Differences from the source:
--   - encoding: f with coefficients of O(n) bits; fix d → for every d ≥ 1 and c, one machine and K for all monic f of natDegree d with |coefficients| < 2^{c(n+1)}; reason: the O(n) constant is fixed with d, as the O_d of the bound allows
--   - encoding: r_p = #{u ∈ ℤ/pℤ : f(u) ≡ 0 (mod p)} → rootCount f p = #{u ∈ [0, p) : p ∣ f(u)}; reason: residues represented by 0 ≤ u < p; the same number
--   - encoding: decide whether some prime qualifies, and if so find the least one → output none, or some p with p the least qualifying prime; reason: one answer carries both the decision and the least prime
--   - encoding: poly(n + L) 2^{O_d(n/√log n)} and polynomial space → K (n+L+1)^K 2^{K n/√(log₂ n)} steps and K (n+L+1)^K cells, K depending on d; reason: one constant for both factors; same instances
--   - encoding: f irreducible modulo p → Irreducible (f.map (Int.castRingHom (ZMod p))) in (ℤ/pℤ)[X]; reason: the reduction of f modulo p
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 8.2, pp.35–36 (PDF pp.37–38); proof p.36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_Supplement_rootCount
import Definitions.Def_SubexpPrimes_Supplement_IsLeastOrNone

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 8.2 (Primes with a prescribed number of roots)** — Gajulapalli, *Deterministic
Construction of Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), pp.35–36.

Fix `d ≥ 1`. Let `C` be admissible of length `L`, let `f ∈ ℤ[X]` be monic of degree `d` with
coefficients of `O(n)` bits, and let `r₀ ∈ {0, …, d}`. One can decide whether some prime `p < 2ⁿ` with
`C(p) = 1` has `r_p = r₀`, and if so find the least one, in time `poly(n + L) 2^{O_d(n/√log n)}` and
polynomial space. In particular, for a monic cubic `f` one can find the least prime `p < 2ⁿ`
satisfying `C` modulo which `f` is irreducible, or decide that there is none.

**Formalization Note.** "`O(n)` bits" is: for a constant `c` fixed with `d`, every coefficient has
absolute value below `2^{c(n+1)}`. The machine and `K` are chosen after `d`, `c` and the admissible
family (published `Admissible`, Definition 2.3), before `n`, the description, `f` and `r₀`. `C(p)` is
`C n e (bitsOf n p)`, the `n`-bit string of `p`, most significant bit first. `r_p` is `rootCount f p`
(distinct roots in `ℤ/pℤ`). The input is `(1ⁿ, description)`, the coefficient list of `f`
(`coeffWord`) and `r₀` in unary; the output is `none`/`some p` (`natOptWord`). Time
`K (n+L+1)^K 2^{K n/√(log₂ n)}` (`subexpBound`), space `K (n+L+1)^K` (`polyBound`). The cubic clause
states irreducibility of `f mod p` in `(ℤ/pℤ)[X]`. -/
theorem theorem_8_2_prescribed_roots :
    (∀ d : ℕ, 1 ≤ d → ∀ c : ℕ,
      ∀ {δ : Type} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop), Admissible encD C →
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          ∀ (n : ℕ) (e : δ) (f : Polynomial ℤ) (r₀ : ℕ),
            f.Monic → f.natDegree = d → (∀ i : ℕ, |f.coeff i| < 2 ^ (c * (n + 1))) → r₀ ≤ d →
            ∃ o : Option ℕ,
              IsLeastOrNone
                {p : ℕ | p.Prime ∧ p < 2 ^ n ∧ C n e (bitsOf n p) ∧ rootCount f p = r₀} o ∧
              RunsWithin M out
                (Encoding.encodeList id
                  [admissibleInput n (encD e), coeffWord f, Encoding.encodeNat r₀])
                (natOptWord o)
                (subexpBound K (n + (encD e).length) n) (polyBound K (n + (encD e).length))) ∧
    (∀ c : ℕ,
      ∀ {δ : Type} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop), Admissible encD C →
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          ∀ (n : ℕ) (e : δ) (f : Polynomial ℤ),
            f.Monic → f.natDegree = 3 → (∀ i : ℕ, |f.coeff i| < 2 ^ (c * (n + 1))) →
            ∃ o : Option ℕ,
              IsLeastOrNone
                {p : ℕ | p.Prime ∧ p < 2 ^ n ∧ C n e (bitsOf n p) ∧
                  Irreducible (f.map (Int.castRingHom (ZMod p)))} o ∧
              RunsWithin M out (Encoding.encodeList id [admissibleInput n (encD e), coeffWord f])
                (natOptWord o)
                (subexpBound K (n + (encD e).length) n)
                (polyBound K (n + (encD e).length))) := by sorry

end SubexpPrimes.Supplement
