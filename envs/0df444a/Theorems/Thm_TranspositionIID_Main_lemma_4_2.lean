-- Prove2me | Theorems.Thm_TranspositionIID_Main_lemma_4_2
-- name    : TranspositionIID.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:18.090211+00:00
-- url     : https://prove2.me/theorems/17f96930-8333-487a-874c-115b159c55a8
-- title:
--   Lemma 4.2 — discrete-time reversible entropy dissipation
-- statement:
--   Let $P$ be any stochastic matrix on a finite space with strictly positive stationary probability $\mu$ and detailed balance. For any initial probability $\nu_0$, put $\nu_s=\nu_0P^s$, $f_s=\nu_s/\mu$, $g_t=(1+f_t+f_{t+1})/3$ and $H=\log(1/\min_z\mu(z))$. For every integer $t\ge0$,
--   $$\mathcal E_P(g_t,\log g_t)\le\frac{H+\log3}{3}\sqrt{\frac{H}{2(t+1)}}.$$
--   No irreducibility, aperiodicity or laziness is assumed. The singleton case has $H=0$. This gives a universal discrete-time bound for the smoothed density.
--
--   Differences from the source:
--   - encoding: finite state space carrying probability laws and a minimum stationary mass → a finite nonempty type, normalized real weights, and sInf of the finite range; reason: a probability law excludes the empty space, and the infimum is its attained minimum
--   - encoding: the evolution nu zero times P to the s and integer t at least zero → finite row matrix powers and natural times; reason: this is exactly the finite marginal law and every source time is nonnegative
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 4.2, printed p.9 = PDF p.9; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_FiniteChain
import Definitions.Def_TranspositionIID_Main_Entropy

namespace TranspositionIID.Main

/-- Lemma 4.2, printed/PDF p.9; includes reducible, periodic and singleton chains. -/
theorem lemma_4_2 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ)
    (ν : S → ℝ) (hν : ActuarialValuation.isFiniteStateDistribution ν) (t : ℕ) :
    GibbsCongestion.dirichletForm P μ (smoothedDensity P μ ν t)
      (fun z => Real.log (smoothedDensity P μ ν t z)) ≤
      ((entropyCeiling μ + Real.log 3) / 3) *
        Real.sqrt (entropyCeiling μ / (2 * ((t : ℝ) + 1))) := by sorry

end TranspositionIID.Main
