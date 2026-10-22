-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_choi_display
-- name    : QRepeaterBench.Dephasing.choi_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:33.278993+00:00
-- url     : https://prove2.me/theorems/8945f07f-c959-420e-9fb7-9af6ee43c603
-- title:
--   Choi matrix of the qudit dephasing channel: ρ_{P_d} = Σ_{m,i,j} (P_m/d) exp[(2iπ/d)(i−j)m] |ii⟩⟨jj| (p. 11)
-- statement:
--   Let $d\ge2$, $p\in[0,1]$, and let $\rho_{\mathcal P_d}=(\mathcal I\otimes\mathcal P_d)(\Psi_d)$ be the Choi matrix of the qudit dephasing channel with weights $P_m=P_m(p,d)$. Then
--
--   $$\rho_{\mathcal P_d}=\sum_{m,i,j=0}^{d-1}\frac{P_m(p,d)}{d}\exp\Big[\frac{2i\pi}{d}(i-j)m\Big]\,|ii\rangle\langle jj| .$$
--
--   Entrywise: the entry of $\rho_{\mathcal P_d}$ in row $|ik\rangle$ and column $|jl\rangle$ is $\sum_m \frac{P_m}{d}\,e^{2\pi i (i-j)m/d}$ when $i=k$ and $j=l$, and $0$ otherwise.
--
--   This explicit form is the starting point for the spectrum of the Choi matrix and for the relative-entropy computation that bounds the entanglement flux.
--
--   **Formalization Note** The left side is the Choi matrix computed from the Kraus form of the channel; the reference is the first tensor factor.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, display between Eqs. (90) and (91)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem choi_display (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i k j l : Fin d) : choi d (dephasing d p) (i, k) (j, l) = if i = k ∧ j = l then ∑ m : Fin d, ((weight d p m : ℂ) / (d : ℂ)) * Complex.exp (2 * Real.pi * Complex.I / (d : ℂ) * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * ((m : ℕ) : ℂ)) else 0 := by sorry
end QRepeaterBench.Dephasing
