-- Prove2me | Theorems.Thm_ShockWear_Inherit_theorem31_1
-- name    : ShockWear.Inherit.theorem31_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:08.15572+00:00
-- url     : https://prove2.me/theorems/a0b9f24b-892d-4ef2-a905-f79d9cfe0726
-- title:
--   Theorem 3.1(3.1) — PF₂ failure probabilities give a PF₂ density
-- statement:
--   Let $\lambda>0$, $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$, and $p_{k+1}=\bar P_k-\bar P_{k+1}$. If the sequence $(p_k)_{k\geq1}$ is PF₂, meaning its successive ratios decrease weakly, then the positive-time density $h$ in (2.3) is PF₂: for every $x>0$ and $0<s\leq t$,
--
--   $$h(x+t)h(s)\leq h(x+s)h(t).$$
--
--   This carries the discrete shape of failure-on-shock probabilities to the continuous lifetime density.
--
--   **Formalization Note** $\bar P_0=1$ removes the atom at the origin. The PF₂ and density ratio conditions are cross-multiplied, including cases where a term vanishes; $h$ is the explicit series (2.3).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1(3.1); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- Theorem 3.1(3.1): discrete PF₂ failure probabilities give a PF₂ density. -/
theorem theorem31_1 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 1 (failProb P)) :
    IsPF2Dens (shockDens lam P) := by sorry

end ShockWear.Inherit
