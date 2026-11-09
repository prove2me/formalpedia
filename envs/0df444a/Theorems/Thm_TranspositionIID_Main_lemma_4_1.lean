-- Prove2me | Theorems.Thm_TranspositionIID_Main_lemma_4_1
-- name    : TranspositionIID.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:06.168587+00:00
-- url     : https://prove2.me/theorems/e1e5c4de-a3c0-4b46-afc4-db7ea19efb13
-- title:
--   Lemma 4.1 — cost bounded by entropy dissipation
-- statement:
--   Let $n\ge1024$, let $p$ be a decreasing strictly positive probability vector, and let $\nu$ be any probability on lists. Write $f(\sigma)=\nu(\sigma)/\mu_p(\sigma)$. Then
--   $$\nu(F_p)\le C_0+\frac32n^5\sqrt{\mathcal E_{P_p}(f,\log f)},\qquad C_0=2+(1+\sqrt e)\left[\tfrac14+\tfrac{2\pi^2}{3}(1+8e)\right].$$
--   Zero density values are allowed. The entropy edge sum and its square root retain $+\infty$ exactly as specified in §2.1. This relates excess cost to local entropy dissipation.
--
--   Differences from the source:
--   - encoding: labels and charged positions 1 through n → labels and positions Fin n with charged position val + 1; reason: the order-preserving shift gives a bijection of all labels and list states
--   - encoding: decreasing relabeling with OPT equal to the sorted positional cost → OPT is the attained minimum over all permutations; reason: sorting shows these are identical, including ties and zeros; no label order is required by the goal
--   - encoding: nonnegative extended entropy edge sum and its square root → ENNReal edge sum, real quantities mapped by ofReal, and rpow with exponent one half; reason: all embedded finite quantities are nonnegative; this preserves the inequality and infinity at one-zero positive-conductance edges
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 4.1, printed p.8 = PDF p.8; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_Buffer
import Definitions.Def_TranspositionIID_Main_Stationary
import Definitions.Def_TranspositionIID_Main_Entropy

namespace TranspositionIID.Main

/-- Lemma 4.1, printed/PDF p.8, including densities with zero values. -/
theorem lemma_4_1 {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (ν : ListState n → ℝ) (hν : ActuarialValuation.isFiniteStateDistribution ν) :
    ENNReal.ofReal (∑ σ, ν σ * excess p σ) ≤
      ENNReal.ofReal C0 + ENNReal.ofReal ((3 / 2 : ℝ) * (n : ℝ) ^ 5) *
        ENNReal.rpow (entropyDissipation (transpositionKernel p) (stationaryLaw p)
          (fun σ => ν σ / stationaryLaw p σ)) (1 / 2) := by sorry

end TranspositionIID.Main
