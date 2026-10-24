-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_local_entropy_bounds
-- name    : QAlgorithms.Papers.Independent.Support50.P42.local_entropy_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:13:35.022174+00:00
-- url     : https://prove2.me/theorems/4f362c48-80c9-4526-9bce-b455daa63461
-- title:
--   Entropy bounds for local treatment and unitary invariance
-- statement:
--   Let $|\psi\rangle$ be a normalized pure state on positive finite-dimensional systems $A,B$. Let Alice apply a complete finite rectangular Kraus family $A_j:A\to A'$, retaining environments or refining outcomes so that each conditional joint state is pure. Write $p_j$ for its Born probability, $\rho_{B,j}$ for the conditional Bob density, $E=S(\rho_B)$, and $H(p)=-\sum_jp_j\log_2p_j$. Zero-probability terms contribute zero. Then
--
--   $$\sum_jp_j\rho_{B,j}=\rho_B,\qquad E-H(p)\le\sum_jp_jS(\rho_{B,j})\le E.$$
--
--   A local unitary leaves Bob's marginal unchanged and conjugates Alice's marginal by that unitary, preserving its spectrum. For every finite adaptive local protocol with pure input and positive-weight pure final leaves, the expected final entanglement is at most the initial entanglement. These statements distinguish unconditional marginal invariance from changes in conditional marginals.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 6, §II: local-treatment entropy interval and invariance

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

/-- PDF p.6: entropy interval, unconditional no-signalling marginal, unitary
marginal/spectral invariance, and the iterated pure-output upper bound.
Refined Kraus outcomes keep the complete conditional joint state pure. -/
theorem local_entropy_bounds {a b c k : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (psi : Vec (Fin a × Fin b)) (hnorm : ‖psi‖=1)
    (A : Fin k → Matrix (Fin c) (Fin a) ℂ) (hA : IsKrausFamily A) :
    let p := fun j => ‖aliceKetBranch (A j) psi‖^2
    let rho := fun j => ((p j : ℂ)⁻¹) • pureDensity (aliceKetBranch (A j) psi)
    (∑ j, (p j : ℂ) • traceLeft (rho j))=traceLeft (pureDensity psi) ∧
    vnEntropy (traceLeft (pureDensity psi))-outcomeEntropy p≤
      (∑ j, p j*vnEntropy (traceLeft (rho j))) ∧
    (∑ j, p j*vnEntropy (traceLeft (rho j)))≤vnEntropy (traceLeft (pureDensity psi)) ∧
    (∀ U : Matrix.unitaryGroup (Fin a) ℂ,
      traceLeft (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=traceLeft (pureDensity psi) ∧
      traceRight (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=
        (U : Op (Fin a))*traceRight (pureDensity psi)*(U : Op (Fin a))ᴴ) ∧
    (∀ s : Shared, IsPureShared s → ∀ out : List (ℝ × Shared), LocalTree s out →
      (∀ w∈out, 0<w.1 → IsPureShared w.2) →
        (out.map fun w => w.1*ent w.2).sum≤ent s) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
