-- Prove2me | Theorems.Thm_TranspositionIID_Main_proposition_3_4
-- name    : TranspositionIID.Main.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:05.186945+00:00
-- url     : https://prove2.me/theorems/609a4eae-4498-4f5e-8ec0-75d3b93675ef
-- title:
--   Proposition 3.4 — auxiliary smoothing and Dirichlet comparison
-- statement:
--   Let $n\ge1024$ and $p$ be a decreasing strictly positive probability vector. For every $x\in\mathbb R$ and $0<\theta\le1/2$, both statements hold:
--   $$ (B_{x,\theta}^{n^4}J_{x,\theta})(\sigma)\le\tfrac14+\frac{\pi^2}{6\theta^2}\qquad\text{for every list }\sigma; $$
--   $$\mathcal E_{B_{x,\theta}}(v,v)\le2n^2e^{-x}\mathcal E_{P_p}(v,v)\qquad\text{for every real function }v.$$
--   Both forms use the same explicitly constructed stationary probability $\mu_p$. The auxiliary chain may be reducible.
--
--   Differences from the source:
--   - encoding: labels and charged positions 1 through n → labels and positions Fin n with charged position val + 1; reason: the order-preserving shift gives a bijection of all labels and list states
--   - encoding: the auxiliary operator B to the n to the fourth power acting on J → expectedAfter for the explicit auxiliary kernel at natural time n ^ 4; reason: the row of the finite matrix power is exactly the auxiliary-chain law from the given permutation
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Proposition 3.4, printed p.6 = PDF p.6; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_Auxiliary
import Definitions.Def_TranspositionIID_Main_Entropy

namespace TranspositionIID.Main

/-- Proposition 3.4, printed/PDF p.6, both (3.2) and (3.3). -/
theorem proposition_3_4 {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (x θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) :
    (∀ σ : ListState n,
      expectedAfter (auxiliaryKernel p x θ) σ (n ^ 4) (separatedInversions p x θ) ≤
        1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2)) ∧
    (∀ v : ListState n → ℝ,
      GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
        2 * (n : ℝ) ^ 2 * Real.exp (-x) *
          GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v) := by sorry

end TranspositionIID.Main
