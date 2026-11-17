-- Prove2me | Theorems.Thm_StretchDepth_Supplement_theorem_2
-- name    : StretchDepth.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:12:53.326342+00:00
-- url     : https://prove2.me/theorems/0a876851-2162-4e6a-ab61-3f6107c38407
-- title:
--   Theorem 2 — necessary depth of PRG-to-PRF constructions, $t\le(k+O(\log ntqd))(N/(n-O(\log ntq)))^d$
-- statement:
--   For every exponent $a>0$ there are constants $\delta,C_1,C_2>0$ such that the following holds. Let $(F,R)$ be a PRG-to-PRF construction with nonadaptive security and parameters $(q,t,0.9,\epsilon,d)$ (Definition 4: $N>n$, $k,\ell,q,d\ge1$, $1\le t\le2^\ell$, $0<\epsilon\le1$) with **polynomial loss** $q\le(nt)^a$, $\epsilon^{-1}\le(nt)^a$, and with $\log_2(ntq)\le\delta n$. Then $n-C_2\log_2(ntq)>0$ and
--   $$
--   t\le\big(k+C_1\log_2(ntqd)\big)\left(\frac{N}{n-C_2\log_2(ntq)}\right)^{d}.
--   $$
--
--   The number $t$ of queries a PRF built in depth $d$ from a PRG can withstand is therefore at most exponential in $d$; in the standard regime $t=n^{\omega(1)}$ this matches the known constructions (Proposition 1).
--
--   **Formalization Note** No $n\ge1$ is assumed: $q\le(nt)^a$ with $q\ge1$ forces it.
--
--   Differences from the source:
--   - reading: polynomial loss $q,\epsilon^{-1}\le(nt)^{O(1)}$ → for each fixed exponent $a>0$, $q,\epsilon^{-1}\le(nt)^a$, the constants depending on $a$; reason: the $O(1)$ exponent is a fixed constant of the construction family.
--   - reading: $\log(ntq)=o(n)$ → $\log_2(ntq)\le\delta n$ for a constant $\delta>0$ chosen with the other constants; reason: a family with $\log(ntq)=o(n)$ satisfies the bound for all large $n$, so the uniform form implies the asymptotic one.
--   - reading: the two $O(\cdot)$ → constants $C_1,C_2>0$ fixed before the instance, $\log=\log_2$; reason: the universal-constant reading of Theorem 1.
--   - encoding: the bound alone → the bound together with $n-C_2\log_2(ntq)>0$; reason: the page's denominator is positive in its regime, and a nonpositive denominator would make the bound meaningless in Lean.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), §4.1, Theorem 2 and the definition of polynomial loss, p.21 (PDF p.21)

import Definitions.Def_StretchDepth_Supplement_IsPRFConstruction

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- **Theorem 2 (Necessary depth) of PRG-to-PRF constructions.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), §4.1, p.21: "we say that a reduction has polynomial loss if q, ϵ⁻¹ ≤ (nt)^{O(1)}.
Theorem 2 (Necessary depth). Any polynomial-loss PRG-to-PRF construction with parameters
(q, t, 0.9, ϵ, d), q, d ≥ 1, and log(ntq) = o(n) satisfies
t ≤ (k + O(log(ntqd))) (N/(n − O(log(ntq))))^d."

**Formalization Note.** Polynomial loss is a fixed exponent `a > 0` with `q, ϵ⁻¹ ≤ (nt)^a`; the
constants may depend on `a`, so `∀ a` comes first. "`log(ntq) = o(n)`" is the uniform form
`log₂(ntq) ≤ δn` for a constant `δ > 0` chosen with the other constants: a family with
`log(ntq) = o(n)` satisfies it for all large `n`, so this implies the asymptotic reading. The two
`O(·)` constants come before the instance; `log = log₂`. The conclusion also states that the
denominator is positive. The conditions of Definition 4 (`N > n`, `k, ℓ, q, d ≥ 1`, `1 ≤ t ≤ 2^ℓ`,
`0 < ϵ ≤ 1`) are binders; `γ = 0.9` is `9/10`. No `n ≥ 1` is assumed: `q ≤ (nt)^a` with `q ≥ 1`
forces it. -/
theorem theorem_2 :
    ∀ a : ℝ, 0 < a → ∃ δ C₁ C₂ : ℝ, 0 < δ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n N k ℓ t q d : ℕ) (ε : ℝ) (F : Bits k → Bits ℓ → RoundTree n N 1)
        (R : (Fin t ↪ Bits ℓ) → PMF (Bits N → QProc n N t)),
        n < N → 1 ≤ k → 1 ≤ ℓ → 1 ≤ q → 1 ≤ d → 1 ≤ t → t ≤ 2 ^ ℓ → 0 < ε → ε ≤ 1 →
        (q : ℝ) ≤ ((n : ℝ) * t) ^ a → ε⁻¹ ≤ ((n : ℝ) * t) ^ a →
        Real.logb 2 ((n : ℝ) * t * q) ≤ δ * n →
        IsPRFConstruction F R q (9 / 10) ε d →
        0 < (n : ℝ) - C₂ * Real.logb 2 ((n : ℝ) * t * q) ∧
          (t : ℝ) ≤ ((k : ℝ) + C₁ * Real.logb 2 ((n : ℝ) * t * q * d)) *
            ((N : ℝ) / ((n : ℝ) - C₂ * Real.logb 2 ((n : ℝ) * t * q))) ^ d := by sorry

end StretchDepth.Supplement
