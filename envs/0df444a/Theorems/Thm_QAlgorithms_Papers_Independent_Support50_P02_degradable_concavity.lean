-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_degradable_concavity
-- name    : QAlgorithms.Papers.Independent.Support50.P02.degradable_concavity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:19:59.157635+00:00
-- url     : https://prove2.me/theorems/2ee45fc8-5660-4a2d-bce6-07d10cb594ed
-- title:
--   §7.3: input concavity of coherent information
-- statement:
--   Let $U:A'\to BE$ be an isometry of finite, positive-dimensional complex registers. Write $\mathcal N(\rho)=\operatorname{Tr}_E(U\rho U^\dagger)$ and $\mathcal N^c(\rho)=\operatorname{Tr}_B(U\rho U^\dagger)$ for its receiver channel and complement. Suppose a CPTP map $\mathcal D:B\to E$ satisfies $\mathcal N^c=\mathcal D\circ\mathcal N$. Define $I_c(\rho,\mathcal N)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, with entropy in bits. For density operators $\rho_0,\rho_1$ and $0\le\lambda\le1$,
--   $$\lambda I_c(\rho_0,\mathcal N)+(1-\lambda)I_c(\rho_1,\mathcal N)\le I_c(\lambda\rho_0+(1-\lambda)\rho_1,\mathcal N).$$
--   This is concavity in the input state of a fixed degradable channel, including both endpoints.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 35, §7.3: input concavity of coherent information

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

/-- Concavity in the INPUT of a degradable channel, §7.3, PDF p.35.
This is distinct from background convexity in the channel at fixed input (p.4). -/
theorem degradable_concavity [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (rho0 rho1 : Op A) (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (lambda : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    lambda * inputCoherent U rho0 + (1 - lambda) * inputCoherent U rho1 ≤
      inputCoherent U ((lambda : ℂ) • rho0 + ((1 - lambda : ℝ) : ℂ) • rho1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
