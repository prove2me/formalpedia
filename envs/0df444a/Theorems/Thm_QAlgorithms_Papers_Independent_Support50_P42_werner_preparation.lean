-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_werner_preparation
-- name    : QAlgorithms.Papers.Independent.Support50.P42.werner_preparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:28:32.821368+00:00
-- url     : https://prove2.me/theorems/d9474937-ff32-4e0b-8a5a-66149b04e186
-- title:
--   Elementary random preparation of the fixed Werner state
-- statement:
--   Let $W=I_4/8+|\Psi^-\rangle\langle\Psi^-|/2$, a normalized two-qubit Werner density. For $n\ge0$, choose $n$ independent fair bits $z_i$. At position $i$, use a singlet if $z_i=1$ and locally prepare $I_4/4$ otherwise. If $\omega_z$ is the resulting product state and $K(z)=\sum_i z_i$, then
--
--   $$2^{-n}\sum_z\omega_z=W^{\otimes n},\qquad K(z)\le n,\qquad \mathbb E K=n/2.$$
--
--   For every choice $z$ an actual local protocol prepares $\omega_z$ from exactly $K(z)$ supplied singlets. An initial supply of $n$ is sufficient; $n/2$ is expected consumption, rather than a deterministic budget. This is the elementary preparation in Eq. (11), separate from the improved external results cited later.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 17, §V, Eq.(11): elementary random preparation of the fixed Werner state

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.17, Eq.(11): independent fair local preparation of W tensor n.
Each branch is an actual LOCC protocol consuming its number of singlet choices;
that number is bounded by n and has expectation n/2, never a fixed n/2 budget. -/
theorem werner_preparation (n : ℕ) :
    IsDensityMatrix wernerState ∧
    (((2 : ℝ)^n)⁻¹ : ℂ) • (∑ z : Fin n → Bool, wernerBranch n z)=dimensionedPower wernerState n ∧
    ((2 : ℝ)^n)⁻¹*(∑ z : Fin n → Bool, (downCount z : ℝ))=(n : ℝ)/2 ∧
    (∀ z : Fin n → Bool, downCount z≤n ∧
      ∃ L : Superop (Fin (2^(downCount z)) × Fin (2^(downCount z))) (Fin (2^n) × Fin (2^n)),
        FiniteLOCC L ∧ L (singlets (downCount z))=wernerBranch n z) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
