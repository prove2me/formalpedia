-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_6_1
-- name    : RSSubspaceDesign.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:42:58.637204+00:00
-- url     : https://prove2.me/theorems/0ef1c027-c699-408d-86fe-4556ea61d7c2
-- title:
--   Theorem 6.1 — deterministic list decoding inside a $d$-dimensional $F$-subspace of $F[X]_{<k}$ in $(O(1/\varepsilon))^{O(d)}\,\tilde O(n\,\mathrm{poly}(1/\varepsilon,d,\log|F|))$ time
-- statement:
--   Let $\varepsilon > 0$, let $F$ be a finite field, let $\alpha_1, \dots, \alpha_n \in F$ be distinct, $y \in F^n$, and let $A \subseteq F[X]_{<k}$ be an $F$-linear space of dimension $d$, given by a basis. A deterministic algorithm running in time
--   $$
--   \bigl(O(1/\varepsilon)\bigr)^{O(d)}\cdot \tilde O\bigl(n\,\mathrm{poly}(1/\varepsilon, d, \log|F|)\bigr)
--   $$
--   outputs the set
--   $$
--   \mathcal L := \bigl\{ f \in A : |\{i : f(\alpha_i) = y_i\}| \ge k + \varepsilon n \bigr\}, \qquad |\mathcal L| \le \bigl(O(1/\varepsilon)\bigr)^d .
--   $$
--
--   This is the warm-up for the pruning of Theorem 5.3, over $F$ instead of $K(X)$. It also gives a faster deterministic list decoder for folded Reed–Solomon codes (Corollary 6.2).
--
--   **Formalization Note** $F = \mathbb F_p[Y]/(f)$ is input as $p, f$, its elements in the power basis, and each polynomial of $F[X]_{<k}$ by its $k$ coefficients. The basis is a list of $d$ such polynomials, linearly independent over $F$. One absolute constant $c$ serves every $O$: $(O(1/\varepsilon))^{O(d)}$ is $(c(1+1/\varepsilon))^{cd}$, $\mathrm{poly}(1/\varepsilon, d, \log|F|)$ is $(1/\varepsilon + d + \lfloor\log_2|F|\rfloor + 2)^c$, $\tilde O(N)$ is $c\,N(\log_2(N+2))^c$, and the list bound is $(c/\varepsilon)^d$. The real time bound enters through its floor. There is one machine per $\varepsilon$. $k$ is any natural number; $n \ge 1$. The output lists $\mathcal L$ without repetition.
--
--   Differences from the source:
--   - encoding: a finite field F, the points, y and a basis of A as given objects → F = 𝔽_p[Y]/(f) input as p and a monic irreducible f; elements in the power basis; polynomials of F[X]_{<k} by their k coefficients; one Turing machine with an explicit step bound; reason: every finite field is isomorphic to such an 𝔽_p[Y]/(f); the base mission's machine model
--   - reading: "given ε > 0 … we give a deterministic algorithm" → one machine per ε, uniform over F, n, k, the points, y and the basis; reason: ε sets the algorithm's parameters (t ~ d/ε); every constant of the bound is absolute
--   - encoding: (O(1/ε))^{O(d)} · Õ(n poly(1/ε, d, log|F|)); |L| ≤ (O(1/ε))^d → ⌊(c(1+1/ε))^{cd} · c N (log₂(N+2))^c⌋ with N = n(1/ε + d + ⌊log₂|F|⌋ + 2)^c; (c/ε)^d; c absolute; reason: the O-conventions written out; 1 + 1/ε keeps the factor at least 1 when ε is large, as O(1/ε) does in a running time
--   - encoding: n points (n unrestricted) → 1 ≤ n; reason: the paper's codes have n ≥ 1 (Section 2, 1 ≤ k ≤ n); at n = 0 the printed bound Õ(n · …) is 0 steps, which no machine meets, so the condition only excludes a case where the bound is undefined as a running time
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 6.1, p.25 (PDF 27)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decK
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 6.1 (deterministic list decoding inside an `F`-subspace of `F[X]_{<k}`).**
Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 6.1,
p.25.

Given `ε > 0`, a finite field `F`, distinct evaluation points `α₁, …, αₙ ∈ F`, `y ∈ Fⁿ`, and an
`F`-linear space `A ⊆ F[X]_{<k}` with `dim A = d`, given by a basis, there is a deterministic
algorithm running in `(O(1/ε))^{O(d)} · Õ(n poly(1/ε, d, log |F|))` which outputs
`L := {f ∈ A : |{i : f(αᵢ) = yᵢ}| ≥ k + εn}`, and `|L| ≤ (O(1/ε))^d`.

**Formalization Note.** The finite field is input as a prime `p` and a monic irreducible
`f ∈ 𝔽_p[Y]` (`F = AdjoinRoot f`, `|F| = p^{deg f}`); elements are written in its power basis
(`decK`), polynomials of `F[X]_{<k}` by their `k` coefficients (`decPoly`). The basis is a list of
`d` such polynomials, linearly independent over `F`; `A` is its span. One machine `M` per `ε` (the
algorithm's parameters depend on `ε`); one absolute constant `c` is chosen first and serves every
`O`: `(O(1/ε))^{O(d)}` is `(c(1 + 1/ε))^{cd}` (the `1 +` keeps the factor `≥ 1` for large `ε`),
`poly(1/ε, d, log|F|)` is `(1/ε + d + ⌊log₂|F|⌋ + 2)^c`, `Õ(N)` is `c · N · (log₂(N + 2))^c`, and the
list bound `(O(1/ε))^d` is `(c/ε)^d` as printed. The real time bound enters through its floor (the
step count is an integer). `k` is any natural number. `n ≥ 1`: the paper's codes have `n ≥ 1`
(Section 2), and at `n = 0` the printed bound `Õ(n · …)` is `0` steps, which no machine meets. The
output lists `L` without repetition. -/
theorem theorem_6_1 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ n k : ℕ, 1 ≤ n → ∀ ac : List (List ℕ), IsCoeffList p f n ac →
      Function.Injective (fun i : Fin n => decK p f (ac.getD i [])) →
      ∀ yc : List (List ℕ), IsCoeffList p f n yc →
      ∀ bs : List (List (List ℕ)), (∀ b ∈ bs, IsCoeffList p f k b) →
      LinearIndependent (AdjoinRoot f) (fun i : Fin bs.length => decPoly p f (bs.get i)) →
      ∃ out : List (List (List ℕ)),
        (∀ m ∈ out, IsCoeffList p f k m) ∧
        HMBinPacking.OutputsWithin M
          (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) ac ++
            encList (encList encNat) yc ++ encList (encList (encList encNat)) bs)
          (encList (encList (encList encNat)) out)
          ⌊((c : ℝ) * (1 + 1 / ε)) ^ (c * bs.length) *
            ((c : ℝ) * ((n : ℝ) * (1 / ε + bs.length + Nat.log 2 (p ^ f.natDegree) + 2) ^ c) *
              Real.logb 2 ((n : ℝ) * (1 / ε + bs.length + Nat.log 2 (p ^ f.natDegree) + 2) ^ c
                + 2) ^ c)⌋₊ ∧
        (out.map (decPoly p f)).Nodup ∧
        (∀ P : (AdjoinRoot f)[X], P ∈ out.map (decPoly p f) ↔
          (P ∈ Submodule.span (AdjoinRoot f)
              (Set.range fun i : Fin bs.length => decPoly p f (bs.get i)) ∧
            (k : ℝ) + ε * n ≤
              ((Finset.univ.filter fun i : Fin n =>
                P.eval (decK p f (ac.getD i [])) = decK p f (yc.getD i [])).card : ℝ))) ∧
        (out.length : ℝ) ≤ ((c : ℝ) / ε) ^ bs.length := by sorry

end Supplement

end RSSubspaceDesign
