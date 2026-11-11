-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_D_3
-- name    : SparseWalsh.Approx.lemma_D_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:27.564537+00:00
-- url     : https://prove2.me/theorems/1d18766b-55a2-42da-8a47-abdddfe7130e
-- title:
--   Lemma D.3 — one residual estimate errs by more than ρ with probability at most K/P + ‖η‖²/(Pρ²)
-- statement:
--   Fix a real coefficient vector $c$ on $\mathbb F_2^d$ and a set $S$ of at most $K$ frequencies, and let $\eta$ agree with $c$ outside $S$ and vanish on $S$. Let $P=2^p$ be a power of two, let $C\in\mathbb F_2^{p\times d}$ have independent uniform entries, and let $y$ be uniform in $\mathbb F_2^d$, independent of $C$. For every fixed frequency $a$ and every $\rho>0$,
--   $$\Pr\Big[\big|\chi_a(y)H^c_{C,y}(Ca)-c(a)\big|>\rho\Big]\le\frac KP+\frac{\|\eta\|_2^2}{P\rho^2}.$$
--   If $\eta=0$, the estimate equals $c(a)$ with probability at least $1-K/P$. This single-table bound feeds the median estimator $\mathrm{Est}_E$ used for every coefficient estimate of Algorithm 3.
--
--   Differences from the source:
--
--   - encoding: P a power of two, C ∈ F_2^{(log₂ P)×d} → P = 2^p, C : Matrix (Fin p) (Fin d) (ZMod 2); reason: same objects
--   - encoding: C with independent uniform entries and y uniform, independent of C → the uniform law on the product of matrices and shifts; probabilities as ENNReal; reason: same law
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 43 (PDF p. 46), Lemma D.3

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma D.3** (One residual estimate), p. 43 (PDF p. 46). Fix a real coefficient vector `c`
and a set `S` of at most `K` frequencies; `η` agrees with `c` outside `S` and vanishes on `S`. Let
`P = 2^p` and let `(C, y)` be uniform on `F_2^{p×d} × F_2^d` (independent uniform entries of `C`,
`y` uniform and independent of `C`). For every fixed frequency `a` and every `ρ > 0`,
`Pr[|χ_a(y) H^c_{C,y}(Ca) − c(a)| > ρ] ≤ K/P + ‖η‖₂²/(Pρ²)`; and if `η = 0`, the estimate equals
`c(a)` with probability at least `1 − K/P`. -/
theorem lemma_D_3 {d p K : ℕ} (c : Cube d → ℝ) (S : Finset (Cube d)) (hK : S.card ≤ K)
    (a : Cube d) :
    let η : Cube d → ℝ := fun b => if b ∈ S then 0 else c b
    let law := PMF.uniformOfFintype (Matrix (Fin p) (Fin d) (ZMod 2) × Cube d)
    (∀ ρ : ℝ, 0 < ρ →
      law.toOuterMeasure {t | ρ < |chi a t.2 * coefBucket c t.1 t.2 (t.1 *ᵥ a) - c a|} ≤
        ENNReal.ofReal ((K : ℝ) / 2 ^ p + coefNormSq η / (2 ^ p * ρ ^ 2))) ∧
    (η = 0 →
      ENNReal.ofReal (1 - (K : ℝ) / 2 ^ p) ≤
        law.toOuterMeasure {t | chi a t.2 * coefBucket c t.1 t.2 (t.1 *ᵥ a) = c a}) := by sorry

end SparseWalsh.Approx
