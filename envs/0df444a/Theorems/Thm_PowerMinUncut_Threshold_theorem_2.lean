-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_2
-- name    : PowerMinUncut.Threshold.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:52.916839+00:00
-- url     : https://prove2.me/theorems/e1b20fb3-068b-4014-b279-2c298e744ffc
-- title:
--   Theorem 2 — directional energy: odd f ∈ W^{1,q}(γ_n; S^{k−1}) has E‖Df(X)Z‖^q ≥ C_{k,q}, with equality for normalized projection
-- statement:
--   For integers $q\ge2$ and $n\ge k>q$, every odd $f\in W^{1,q}(\gamma_n;S^{k-1})$ satisfies
--   $$\mathbb E\,\|Df(X)Z\|^q\ \ge\ C_{k,q}=\mathbb E\chi_{k-1}^q\,\mathbb E\chi_k^{-q},$$
--   where $X,Z$ are independent standard Gaussian vectors in $\mathbb R^n$. Normalized projection onto $k$ coordinates, $f_k(x)=x_{1:k}/\|x_{1:k}\|$, attains equality (and is an odd map in $W^{1,q}(\gamma_n;S^{k-1})$).
--
--   The inequality identifies $C_{k,q}$ as the least directional energy of an odd sphere-valued map; Theorem 3 transfers it to arbitrary measurable maps.
--
--   Differences from the source:
--   - encoding: W^{1,q}(γ_n; S^{k−1}), odd → `IsGaussSobolevSphere` (locally integrable f, Df, weak derivative against smooth compactly supported tests, f, Df ∈ L^q(γ_n), ‖f‖ = 1 a.e.) and `IsOddAE`; reason: Lean representation of the Gaussian Sobolev class
--   - encoding: C_{k,q} = Eχ^q_{k−1} Eχ^{−q}_k → C_{k,q} = a(k − 1, q)/b(k − 1, q); reason: a(k − 1, q) = Eχ^q_{k−1} and Eχ^{−q}_k = 2^{−q/2}Γ((k − q)/2)/Γ(k/2) = 1/b(k − 1, q) (p. 5)
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 2, Theorem 2

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance
import Definitions.Def_PowerMinUncut_Threshold_Sobolev

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 2 (directional energy)**, p. 2. For integers `q ≥ 2` and `n ≥ k > q`, every odd
`f ∈ W^{1,q}(γ_n; S^{k-1})` satisfies `E‖Df(X)Z‖^q ≥ C_{k,q} = Eχ_{k-1}^q Eχ_k^{-q}` (`X, Z`
independent standard Gaussian vectors), and normalized projection onto `k` coordinates attains
equality. -/
theorem theorem_2 (q n k : ℕ) (hq : 2 ≤ q) (hkq : q < k) (hnk : k ≤ n) :
    (∀ (f : E n → E k) (Df : E n → (E n →L[ℝ] E k)), IsGaussSobolevSphere q f Df → IsOddAE f →
      Ckp k q ≤ dirEnergy q Df) ∧
    Ckp k q = aFun ((k : ℝ) - 1) q / bFun ((k : ℝ) - 1) q ∧
    ∃ Df : E n → (E n →L[ℝ] E k), IsGaussSobolevSphere q (coordProj n k) Df ∧
      IsOddAE (coordProj n k) ∧ dirEnergy q Df = Ckp k q := by sorry

end PowerMinUncut.Threshold
