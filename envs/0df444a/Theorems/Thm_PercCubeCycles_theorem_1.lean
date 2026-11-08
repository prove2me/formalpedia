-- Prove2me | Theorems.Thm_PercCubeCycles_theorem_1
-- name    : PercCubeCycles.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:50.472911+00:00
-- url     : https://prove2.me/theorems/6c04c3eb-27e1-474d-8c6c-0287c4897686
-- title:
--   Theorem 1 — for $p=(1+\varepsilon)/d$, whp $Q^d_p$ has a cycle of length $\ge C\varepsilon^22^d$, found in $O(d^22^{2d})$ time
-- statement:
--   Let $\varepsilon>0$ be sufficiently small. There exists a constant $C>0$, independent of $\varepsilon$, such that if $p=p(d)=(1+\varepsilon)/d$, then with high probability $Q^d_p$ contains a cycle of length at least
--   $$C\varepsilon^22^d.$$
--   Moreover, such a cycle can be found in $O(d^22^{2d})$ time.
--
--   Together with Theorem 2, this shows that the circumference of $Q^d_p$ is $\Theta(\varepsilon^22^d)$ whp.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - reading: time bound with no machine named → randomized word RAM: for each $\varepsilon$ a program and a constant $K$; whp over the percolation and the coins, the run halts within $Kd^22^{2d}$ steps and outputs a cycle of $Q^d_p$ of length at least $C\varepsilon^22^d$ with the same $C$, for every admissible word width; reason: the paper names no machine; this is the published word RAM with every instruction charged one step
--   - encoding: $Q^d_p$ as input to the algorithm → $d$, then one bit per position $i2^d+c$; reason: a fixed layout of the edge indicators
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 1, p.3

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Percolation
import Definitions.Def_PercCubeCycles_MachineIO

set_option autoImplicit false

open Filter Topology RandomGames.BRD MatroidSensOracle

namespace PercCubeCycles

/-- Theorem 1, p.3, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `ε > 0` be sufficiently small. There is a constant `C > 0` independent of
`ε` such that, for `p = (1 + ε)/d`, whp `Q^d_p` contains a cycle of length at least `Cε²2^d`. Moreover, such
a cycle can be found in `O(d²2^{2d})` time.

**Formalization Note.** The order is `∃ C, ∃ ε₀, ∀ ε`, so `C` does not depend on `ε`. The time clause is
read on the randomized word RAM. The program `P` and the constant `K` are chosen for each `ε`, before `d`
and `ω`. The running time and the correctness of the output hold whp over the percolation and the
coins (p.11: "the claimed running time is `O(d²2^{2d})` whp"), with the same `C`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) (fun d ω => HasCycleAtLeast (openGraph ω) (C * ε ^ 2 * 2 ^ d)) ∧
      ∃ (P : List Instr) (K b : ℕ),
        Tendsto (fun d : ℕ =>
          ((percMeasure (supercritical ε d) d).prod coinLaw)
            {x | ∀ w, WidthOK b (cubeInput x.1) w →
              ∃ mem, exec P x.2 (K * d ^ 2 * 2 ^ (2 * d)) 0 0 (loadWords w (cubeInput x.1)) = some mem ∧
                ∃ c : List (Profile d), IsCycleList (openGraph x.1) c ∧
                  C * ε ^ 2 * 2 ^ d ≤ (c.length : ℝ) ∧
                  OutputsWords mem (c.length :: c.map profileCode)})
          atTop (𝓝 1) := by sorry

end PercCubeCycles
