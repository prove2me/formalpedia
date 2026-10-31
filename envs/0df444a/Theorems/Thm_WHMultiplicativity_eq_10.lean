-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_10
-- name    : WHMultiplicativity.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:19.623295+00:00
-- url     : https://prove2.me/theorems/f368461c-60c8-4653-bd32-927d83675c4a
-- title:
--   Eq. (10): $S\otimes S(|\Phi\rangle\langle\Phi|) = \frac{1}{(d-1)^2}\big(\mathbb 1 - \mathbb 1\otimes\rho - \rho\otimes\mathbb 1 + |\Phi\rangle\langle\Phi|\big)$
-- statement:
--   Let $d\ge 2$ and let $S$ be the Werner–Holevo channel on $d\times d$ matrices. Let $\Phi = \sum_\alpha c_\alpha|\alpha\alpha\rangle \in \mathbb C^d\otimes\mathbb C^d$ be a unit vector in Schmidt diagonal form with respect to the fixed basis, with coefficients $c_\alpha \ge 0$, $\sum_\alpha c_\alpha^2 = 1$, and let $\rho = \sum_\alpha c_\alpha^2|\alpha\rangle\langle\alpha|$ be its reduced density operator. Then
--
--   $$
--   S\otimes S\big(|\Phi\rangle\langle\Phi|\big) = \frac{1}{(d-1)^2}\Big(\mathbb 1 - \mathbb 1\otimes\rho - \rho\otimes\mathbb 1 + |\Phi\rangle\langle\Phi|\Big).
--   $$
--
--   This is the two-copy output on which the counterexample is evaluated.
--
--   **Formalization Note** $S\otimes S$ is the tensor product of superoperators `QAlgorithms.piSuperop`; a basis vector $|\alpha\rangle\otimes|\beta\rangle$ is indexed by $y : \{0,1\}\to\{0,\dots,d-1\}$. The matrix $\mathbb 1\otimes\rho$ has entries $\delta_{y_0y_0'}\,\rho_{y_1y_1'}$ and $\rho\otimes\mathbb 1$ has entries $\rho_{y_0y_0'}\,\delta_{y_1y_1'}$.
--
--   Differences from the source:
--   - encoding: Φ in Schmidt diagonal form Φ = Σ_α c_α|αα⟩ → real c with c α ≥ 0 and Σ_α c α² = 1, Φ y = c (y 0) if y 0 = y 1 else 0, in the standard basis; reason: Schmidt coefficients are nonnegative reals and Φ is a pure state; the covariance reduction to this form is not part of the item
--   - encoding: S ⊗ S on ℂ^d ⊗ ℂ^d → QAlgorithms.piSuperop (fun _ : Fin 2 => S) on matrices indexed by Fin 2 → Fin d; reason: the tensor product of superoperators through matrix units, on every input (entangled ones included); y : Fin 2 → Fin d is the basis vector |y 0⟩ ⊗ |y 1⟩
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (10), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (10), p.2: for a vector in Schmidt diagonal
form `Φ = Σ_α c_α |αα⟩` with reduced density operator `ρ = Σ_α c_α² |α⟩⟨α|`,
`S ⊗ S(|Φ⟩⟨Φ|) = (1/(d − 1)²)(𝟙 − 𝟙 ⊗ ρ − ρ ⊗ 𝟙 + |Φ⟩⟨Φ|)`.

**Formalization Note.** `S ⊗ S` is `QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo d)`,
the tensor product of superoperators on `ℂ^d ⊗ ℂ^d`, whose basis vector `|α⟩ ⊗ |β⟩` is indexed by
`y : Fin 2 → Fin d` with `y 0 = α`, `y 1 = β`. The Schmidt coefficients `c_α` are real,
nonnegative and `Σ_α c_α² = 1` (`Φ` is a unit vector), in the fixed (standard) basis. `𝟙 ⊗ ρ` has
entries `δ_{y₀ y₀'} ρ_{y₁ y₁'}` and `ρ ⊗ 𝟙` has entries `ρ_{y₀ y₀'} δ_{y₁ y₁'}`. The reduction
"due to covariance we may take Φ in Schmidt diagonal form" is not part of the statement.
`2 ≤ d` is the paper's standing assumption. -/
theorem eq_10 (d : ℕ) (hd : 2 ≤ d) (c : Fin d → ℝ) (hc0 : ∀ α, 0 ≤ c α)
    (hc1 : ∑ α, c α ^ 2 = 1) :
    let Φ : (Fin 2 → Fin d) → ℂ := fun y => if y 0 = y 1 then ((c (y 0) : ℝ) : ℂ) else 0
    let ρ : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun α => ((c α ^ 2 : ℝ) : ℂ)
    let oneTensorRho : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
      Matrix.of fun y y' => if y 0 = y' 0 then ρ (y 1) (y' 1) else 0
    let rhoTensorOne : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
      Matrix.of fun y y' => if y 1 = y' 1 then ρ (y 0) (y' 0) else 0
    QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo d) (pureState Φ) =
      (((d : ℂ) - 1) ^ 2)⁻¹ • (1 - oneTensorRho - rhoTensorOne + pureState Φ) := by sorry

end WHMultiplicativity
