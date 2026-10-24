-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_cq_pentagons
-- name    : QAlgorithms.Papers.Independent.Support50.P02.cq_pentagons
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:16:47.62278+00:00
-- url     : https://prove2.me/theorems/4861efd6-283d-44ad-976d-d8ecb181231a
-- title:
--   §6: alternative cq pentagons and second corner
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For a pure ensemble $\{p_x,\phi_x^{A'}\}$ and an independent pure state $\Psi^{BB'}$, let $\sigma^{XBC}=\sum_xp_x|x\rangle\langle x|\otimes(\operatorname{id}_B\otimes\mathcal N)(\phi_x\otimes\Psi)$. Write $H$ for von Neumann entropy in bits, $I(U;V)=H(U)+H(V)-H(UV)$, and $I_c(U\rangle V)=H(V)-H(UV)$.
--
--   Let $\mathcal P_{cq}(\mathcal M)$ be the union over these inputs of the nonnegative pairs satisfying
--   $$r\le I(X;BC)_\sigma,\quad S\le I_c(B\rangle CX)_\sigma,\quad r+S\le I(X;C)_\sigma+I_c(B\rangle CX)_\sigma.$$
--   Then
--   $$CQ(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal P_{cq}(\mathcal N^{\otimes k})}.$$
--   On each such state, the sum bound also equals $I(X;BC)_\sigma+I_c(B\rangle C)_\sigma$. Whenever $I_c(B\rangle C)_\sigma\ge0$, the second corner $(I(X;BC)_\sigma,I_c(B\rangle C)_\sigma)$ belongs to $CQ(\mathcal N)$. This records both the alternative characterization and its operational nonnegative second corner.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 30, §6: alternative cq pentagons and second corner

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

/-- Alternative cq pentagons and their second corner, PDF pp.30–31.
All terms use one ensemble and independent Bob state; the corner is operational
only when its quantum coordinate is nonnegative. -/
theorem cq_pentagons [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    cqMacCapacity N = closure (regularized (fun n => cqPentagons (macPower N n))) ∧
    (∀ D : CQMacData A B, D.classical N + D.conditionalCoherent N =
      D.sideClassical N + D.coherent N) ∧
    (∀ D : CQMacData A B, 0 ≤ D.coherent N →
      (D.sideClassical N, D.coherent N) ∈ cqMacCapacity N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
