-- Prove2me | Theorems.Thm_VirialTheorem_virial_theorem_power_law
-- name    : VirialTheorem.virial_theorem_power_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T19:18:42.306555+00:00
-- url     : https://prove2.me/theorems/c6c6db78-e70c-44d1-8c85-c14cfc8e66df
-- title:
--   Virial theorem for power-law forces: $\langle T\rangle_\tau-\tfrac n2\langle V_{\mathrm{TOT}}\rangle_\tau\to0$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Suppose the particles interact only through power-law pair potentials $V_{jk}(s)=\alpha_{jk}s^n$ ($\alpha_{jk}=\alpha_{kj}$): for all $t\ge0$ the momentum $p_k$ has derivative equal to the net pair force at the configuration $r(t)$, and $\dot r_k=v_k$ for all $t$. Suppose the motion is collision-free ($r_j(t)\ne r_k(t)$ for $j\ne k$, $t\ge0$) and bounded ($\|r_k(t)\|,\|v_k(t)\|\le C$ for $t\ge0$). Then
--   $$\lim_{\tau\to\infty}\Big(\langle T\rangle_\tau-\frac n2\langle V_{\mathrm{TOT}}\rangle_\tau\Big)=0 .$$
--
--   **Formalization Note** The limit statement is the precise content of "$\langle T\rangle=\frac n2\langle V_{\mathrm{TOT}}\rangle$ for stably bound systems"; the individual averages need not converge.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Time averaging' (power-law forces)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virial_theorem_power_law {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space)
    (α : Fin N → Fin N → ℝ) (n : ℝ)
    (hα : ∀ j k, α j k = α k j)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k, ∀ t ≥ 0, HasDerivAt (fun s => m k • v k s)
      (netPairForce (powerLawPotential α n) (fun i => r i t) k) t)
    (hx : ∀ t ≥ 0, ∀ j k, j ≠ k → r j t ≠ r k t)
    (hbdd : ∃ C : ℝ, ∀ t ≥ 0, ∀ k, ‖r k t‖ ≤ C ∧ ‖v k t‖ ≤ C) :
    Tendsto (fun τ => timeAverage (kineticEnergy m v) τ -
        (n / 2) * timeAverage (fun t => totalPotential (powerLawPotential α n)
          (fun i => r i t)) τ) atTop (𝓝 0) := by sorry

end VirialTheorem
