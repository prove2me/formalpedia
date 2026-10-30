-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition2
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:47:09.281068+00:00
-- url     : https://prove2.me/theorems/c1b9e305-1b41-42f1-abd9-9669875d0ff4
-- title:
--   Proposition 2 (short and extended): eigenvalues with multiplicities
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $B_{an}=V^{t_n}(a,n)$ be the unnormalized Bell operator and $\eta=\sum_aB_{an}$. Construct $\eta(\alpha)$ by Eq.(7), $M_\alpha$ as its actual range projection, and $F_\mu(\alpha)=M_\alpha(P_\mu\otimes I)$. The physical block spectrum is
--
--   $$\eta=\sum_{\alpha}\sum_{\mu\in\alpha}\gamma_\mu(\alpha)F_\mu(\alpha),\qquad \gamma_\mu(\alpha)=N\frac{m_\mu d_\alpha}{m_\alpha d_\mu}=d+C_\mu-C_\alpha>0.$$
--
--   Here $C_\lambda=\sum_{i<j}\chi_\lambda((ij))/d_\lambda$; this equals the printed transposition-character coefficient when the degree is at least two. Each $F_\mu(\alpha)$ is an orthogonal projector of rank $m_\alpha d_\mu$, and $\eta F_\mu(\alpha)=\gamma_\mu(\alpha)F_\mu(\alpha)$. For $\rho=\eta/d^N$ the same blocks have eigenvalue $\gamma_\mu(\alpha)/d^N$. The complement is explicitly retained: $\eta(I-\operatorname{supp}\eta)=0$. This describes the nonzero blocks and retains the complementary zero sector.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 9, Proposition 2 (short and extended): eigenvalues with multiplicities

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.9–10 Proposition2 (and short p.4): complete physical nonzero
block spectrum, including multiplicities and rho's d^(-N) scaling. -/
theorem proposition2 (d k : ℕ) (hd : 2 ≤ d) :
    pbtSwapSum d k = (∑ a : Schur.Partition d (k+1),
      ∑ b : Schur.Partition d (k+2), if Extends a b then
        (pbtBlockEigenvalue a b : ℂ) • fBlock a b else 0) ∧
    pbtSwapSum d k * (1 - support (pbtSwapSum d k)) = 0 ∧
    (∀ a : Schur.Partition d (k+1), ∀ b : Schur.Partition d (k+2), Extends a b →
      0 < mult a ∧ 0 < mult b ∧ 0 < sdim a ∧ 0 < sdim b ∧
      0 < pbtBlockEigenvalue a b ∧
      pbtBlockEigenvalue a b = ((k+2:ℕ):ℝ) * (mult b:ℝ) * sdim a / ((mult a:ℝ) * sdim b) ∧
      pbtBlockEigenvalue a b = (d:ℝ) + classScalar b - classScalar a ∧
      (fBlock a b).IsHermitian ∧ fBlock a b * fBlock a b = fBlock a b ∧
      Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (fBlock a b))) =
        sdim b * mult a ∧
      pbtSwapSum d k * fBlock a b = (pbtBlockEigenvalue a b:ℂ) • fBlock a b ∧
      ((1/(d:ℂ)^(k+2)) • pbtSwapSum d k) * fBlock a b =
        ((pbtBlockEigenvalue a b / (d:ℝ)^(k+2):ℝ):ℂ) • fBlock a b) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
