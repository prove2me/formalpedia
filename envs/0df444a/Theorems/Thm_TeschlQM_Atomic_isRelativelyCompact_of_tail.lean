-- Prove2me | Theorems.Thm_TeschlQM_Atomic_isRelativelyCompact_of_tail
-- name    : TeschlQM.Atomic.isRelativelyCompact_of_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:11:47.296278+00:00
-- url     : https://prove2.me/theorems/05c9c1f4-897a-4295-be3d-2e2873d5a3cf
-- title:
--   Lemma 11.5 — H₀-bound 0 plus decay at infinity gives H₀-compactness
-- statement:
--   Let $V$ be a multiplication operator in $L^2(\mathbb R^n)$ which is $H_0$ bounded with $H_0$-bound $0$, and suppose that
--   $$\|\chi_{\{x \mid |x| \ge R\}} V R_{H_0}(z)\| \to 0 \quad \text{as } R \to \infty$$
--   for some $z \in \rho(H_0)$. Then $V$ is relatively compact with respect to $H_0$.
--
--   In the proof of the HVZ theorem this handles the singular localized terms $\varphi_j^2 V_j$, which vanish at infinity in the relevant directions but are not bounded.
--
--   **Formalization Note.** $V$ is multiplication (`mulOp`) by a measurable `V : EuclideanSpace ℝ (Fin n) → ℂ`. $z$ and the resolvent $R = R_{H_0}(z)$ are given with `IsResolventAt`. The operator-norm convergence is written out: for every $\varepsilon > 0$ there is $R_0$ such that for all $r \ge R_0$ and all $\varphi \in L^2$, $\|\chi_{\{|x| \ge r\}} V R_{H_0}(z)\varphi\|_2 \le \varepsilon\|\varphi\|$ (as an `eLpNorm` of the function $x \mapsto \chi_{\{|x|\ge r\}}(x) V(x) (R\varphi)(x)$).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 244, Lemma 11.5

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_Shared_relativeBound
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian

namespace TeschlQM.Atomic

open MeasureTheory

/-- Teschl, Lemma 11.5, p. 244. Let `V` be a multiplication operator (by a measurable function)
in `L²(ℝⁿ)` which is `H₀` bounded with `H₀`-bound `0`, and suppose that
`‖χ_{\{x | |x| ≥ R\}} V R_{H₀}(z)‖ → 0` as `R → ∞` for some `z ∈ ρ(H₀)` with resolvent
`R_{H₀}(z)`. Then `V` is relatively compact with respect to `H₀`.
The operator-norm convergence is written out: for every `ε > 0` there is `R₀` such that for all
`r ≥ R₀` and all `φ ∈ L²`, `‖χ_{\{|x| ≥ r\}} V R_{H₀}(z) φ‖ ≤ ε ‖φ‖`. -/
theorem isRelativelyCompact_of_tail {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℂ)
    (hVm : Measurable V)
    (hV : TeschlQM.Shared.relativeBound (freeHamiltonian (Fin n)) (mulOp volume V) = 0)
    (z : ℂ) (R : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hR : TeschlQM.Shared.IsResolventAt (freeHamiltonian (Fin n)) z R)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r →
      ∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
        eLpNorm (Set.indicator {x | r ≤ ‖x‖}
          (fun x => V x * (R φ : EuclideanSpace ℝ (Fin n) → ℂ) x)) 2 volume ≤
          ENNReal.ofReal (ε * ‖φ‖)) :
    TeschlQM.Shared.IsRelativelyCompact (mulOp volume V) (freeHamiltonian (Fin n)) := by sorry

end TeschlQM.Atomic
