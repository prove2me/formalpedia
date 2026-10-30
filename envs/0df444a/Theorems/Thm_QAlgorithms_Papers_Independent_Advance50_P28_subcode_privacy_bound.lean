-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_subcode_privacy_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.subcode_privacy_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:58:29.686431+00:00
-- url     : https://prove2.me/theorems/9b88965e-7ddb-41cb-9fa2-df3773fe85ea
-- title:
--   Theorem 6 (87)
-- statement:
--   Let $G$ be a finite abelian additive group, $C_1\le G$ a fixed subgroup, and $W$ a fixed classical channel with measurable output densities. Let an independent public seed choose $C_2(X)\le C_1$, always of size $L\ge1$, with $\Pr\{x\in C_2(X)\}\le L/|C_1|$ for every nonzero $x\in C_1$. Encode each uniform coset key by the uniform law on that coset. There are $|C_1|/L$ keys and
--   $$\mathbb E_Xd_1(\Phi_{C_1,C_2(X)}|E)\le3\frac{\exp\phi(t|W,U_{C_1})}{L^t}\quad(0\le t\le1/2).$$
--   The averaged leakage includes the public seed. This theorem supplies secrecy for a fixed main code without a reliability assertion; subgroups are equivalently submodules over the integers. Here $U_{C_1}$ is uniform on $C_1$ and $\phi(t|W,q)=\log\int(\sum_xq(x)W_x(y)^{1/(1-t)})^{1-t}\,dy$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 15, Theorem 6 (87)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.15, Theorem 6, (87): arbitrary fixed main code; no Bob-error
claim. Only additive-group structure of the modules is used. -/
theorem subcode_privacy_bound {G E S : Type*} [AddCommGroup G] [Fintype G]
    [Fintype S] [Nonempty S] [MeasurableSpace E]
    (mu : Measure E) (W : G → E → ℝ≥0∞) (hW : IsDensityChannel mu W)
    (C1 : AddSubgroup G) (H : S → AddSubgroup C1) (w : S → ℝ)
    (L : ℕ) (hL : 0 < L) (hcond : SubcodeCondition C1 H w L) :
    (∀ seed, Nat.card (C1 ⧸ H seed) = Fintype.card C1 / L) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), expectedCosetLeakage mu W C1 H w ≤
      3 * gallagerDensityMoment mu W (subgroupUniform C1) t / (L : ℝ≥0∞) ^ t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
