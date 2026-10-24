-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_phaseflip_qq
-- name    : QAlgorithms.Papers.Independent.Support50.P02.phaseflip_qq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:19:22.088234+00:00
-- url     : https://prove2.me/theorems/59575a1a-609e-4569-af7f-f8e52258fbef
-- title:
--   §7.2: collective phase-flip qq capacity
-- statement:
--   Let $0\le p\le1$ and let $\mathcal N_p$ act on the two input qubits by
--   $$\mathcal N_p(\rho)=(1-p)\rho+p(Z\otimes Z)\rho(Z\otimes Z),$$
--   where $Z=\operatorname{diag}(1,-1)$. Its unassisted qq capacity region, using separate encoders, untouched independent references, one joint decoder, and one squared joint fidelity, is
--   $$Q(\mathcal N_p)=\{(R,S)\in\mathbb R_{\ge0}^2:R\le1,\ S\le1,\ R+S\le2-H_2(p)\}.$$
--   Here $H_2$ is binary entropy in bits. This is a full single-letter capacity equality, including $p=0,1$ and $p=1/2$.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 8, §7.2: collective phase-flip qq capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Full single-letter qq capacity for the collective phase-flip channel,
PDF p.8 and §7.2 p.34; endpoints p=0,1 and p=1/2 are included. -/
theorem phaseflip_qq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    qqMacCapacity (collectivePhase p) =
      {r | Nonnegative r ∧ r.1 ≤ 1 ∧ r.2 ≤ 1 ∧ r.1 + r.2 ≤ 2 - binEntropy2 p} := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
