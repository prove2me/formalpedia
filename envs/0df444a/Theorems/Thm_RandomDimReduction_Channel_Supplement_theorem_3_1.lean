-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_Supplement_theorem_3_1
-- name    : RandomDimReduction.Channel.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:43:21.695247+00:00
-- url     : https://prove2.me/theorems/21850932-81d8-48a0-bafd-b9b0d2f37cae
-- title:
--   Theorem 3.1 — random purification from dimension reduction
-- statement:
--   Let $n,k,d$ be positive integers with $k\le d$. Use the three explicit maps of Eqs. (4)–(5), defined from the unnormalized reference-first Choi operator of the published $R$. The map $P^{CPTP}$ is complex-linear, completely positive and trace preserving on every operator.
--
--   For every density operator $\rho$ on $\mathbb C^d$ of actual matrix rank at most $k$, and every fixed unit purification $\phi\in\mathbb C^d\otimes\mathbb C^k$ of $\rho$,
--   $$P^{CPTP}(\rho^{\otimes n})=P^{CP}(\rho^{\otimes n})=P(\rho^{\otimes n})=\int\big((I\otimes V)|\phi\rangle\langle\phi|(I\otimes V^\dagger)\big)^{\otimes n}\,dV.$$
--   Here $dV$ is normalized Haar on $U(k)$, a single sampled $V$ is used in all copies, and paired registers are canonically regrouped. This identifies the explicit Choi extension as a rank-dependent random purification channel.
--
--   Differences from the source:
--   - encoding: the explicit function P^CPTP is a quantum channel → a bundled complex-linear CPTP map agrees with the explicit Eq. (5) function on every operator; reason: the equality makes linearity and full-domain CPTP validity conclusions rather than assumptions
--   - encoding: the n-fold tensor power of a purification on paired registers → canonical reindexing from (A tensor B)^n to A^n tensor B^n; reason: both sides of Eq. (6) must use the same physical registers
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Theorem 3.1, p. 9

import Definitions.Def_RandomDimReduction_Channel_Supplement_Purification

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel.Supplement

/-- Theorem 3.1, pp.9–10, Eq.(6). Linearity and CPTP validity of the explicit Eq.(5)
function are conclusions, expressed by its equality with a bundled CPTP linear map. -/
theorem theorem_3_1 (n k d : ℕ) (hn : 0 < n) (hk : 0 < k) (hkd : k ≤ d) :
    (∃ Phi : Op (Word n d) →ₗ[ℂ] Op (Word n d × Word n k),
      (∀ X, Phi X = purificationCPTP n k d X) ∧ WildeQIT.EntBreaking.IsQuantumChannel Phi) ∧
    ∀ rho : Op (Fin d), MixedCloning.Optimal.IsState rho → rho.rank ≤ k →
      ∀ phi : EuclideanSpace ℂ (Fin d × Fin k), IsPurification rho phi →
        purificationCPTP n k d (tensor n rho) = purificationCP n k d (tensor n rho) ∧
        purificationCP n k d (tensor n rho) = purification n k d (tensor n rho) ∧
        purification n k d (tensor n rho) = randomPurificationAverage n phi := by sorry

end RandomDimReduction.Channel.Supplement
