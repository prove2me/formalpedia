-- Prove2me | Theorems.Thm_RadGauss_RiskBound_bounded_difference
-- name    : RadGauss.RiskBound.bounded_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:21:58.821997+00:00
-- url     : https://prove2.me/theorems/59000087-611d-4c6e-9307-3791491bfd7f
-- title:
--   Proof of Theorem 8 — $\sup_{h\in\tilde\phi\circ F}(\mathbf Eh-\hat{\mathbf E}_nh)$ changes by at most $2/n$
-- statement:
--   Let $P$ be a probability measure on $\mathcal X \times \mathcal Y$, let $\phi : \mathcal Y \times \mathcal A \to [0, 1]$ be measurable, and let $F$ be a class of measurable maps $\mathcal X \to \mathcal A$. For a sample $S = ((X_1, Y_1), \dots, (X_n, Y_n))$ write
--
--   $$\Phi(S) = \sup_{h \in \tilde\phi\circ F}\bigl(\mathbf E h - \hat{\mathbf E}_n h\bigr).$$
--
--   Then replacing any single example $(X_i, Y_i)$ of the sample by an arbitrary $z' \in \mathcal X \times \mathcal Y$ changes $\Phi$ by at most $2/n$:
--
--   $$\bigl|\Phi(S) - \Phi(S^{(i \leftarrow z')})\bigr| \le \frac{2}{n}.$$
--
--   This is the bounded-difference condition that lets McDiarmid's inequality be applied to the uniform deviation.
--
--   **Formalization Note** The class $\tilde\phi\circ F$ takes values in $[-1, 1]$ because $\phi$ does in $[0,1]$. The statement is also true for empty $F$ (both suprema are the Lean default $0$), so no nonemptiness hypothesis is added; for $n = 0$ there is no index and it is vacuous. Measurability of $\phi$ and of the members of $F$ is the paper's implicit convention.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 467 (PDF p. 5), proof of Theorem 8, sentence after the first display

import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 467), bounded differences: for a cost `φ` with values in `[0, 1]`,
replacing one example `(X_i, Y_i)` of the sample by any `z'` changes the uniform deviation
`sup_{h ∈ φ̃∘F} (E h − Ê_n h)` by at most `2/n`. -/
theorem bounded_difference {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin n → X × Y) (i : Fin n) (z' : X × Y) :
    |supDev P n (phiTildeComp φ F) S - supDev P n (phiTildeComp φ F) (Function.update S i z')|
      ≤ 2 / n := by sorry

end RadGauss.RiskBound
