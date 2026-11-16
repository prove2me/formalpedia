-- Prove2me | Theorems.Thm_PolyEulerFlow_Supplement_theorem_22
-- name    : PolyEulerFlow.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:11:16.975512+00:00
-- url     : https://prove2.me/theorems/241927f5-c191-46cc-99d6-6cea10d6e4ba
-- title:
--   Theorem 22 — a quartic certificate and the contract of cycles keep the branching controller (14) on its two-cycle
-- statement:
--   Fix an integer $K\ge256$. The quartic (15) is $P(Y)=2304Y^4-4608Y^3+3296Y^2-992Y+105$, of degree four with five coefficients. There are $s_0\in\mathbb N$ and $B>0$ such that for every $s\ge s_0$, with $h=2^{-s}$, $\varepsilon=h^K$ and
--   $$d_s=B\,\Delta_\varepsilon,\qquad\Delta_\varepsilon=\big(1+\log(1/\varepsilon)\big)\big(\varepsilon^{1/4}+\varepsilon^2\big),$$
--   one has $d_s\le1/48$, and the following holds for every rational $a\in[5/16,3/8]\cup[5/8,11/16]$.
--
--   Initialize the unchanged compiler (14) by $p=(1,0,0,0)$, $\tau_i=\varepsilon$, $Y=Y^s=a$, $v=(a-1/2)/4$, and allow any initial point $z_0$ within $\varepsilon^2/16$ of it in sup norm over the eleven active coordinates. Let $c_0=1/3$ if $a<1/2$ and $c_0=2/3$ otherwise, $c_{j+1}=1-c_j$, and let the components alternate starting from that of $a$ ($C_-=[1/4,5/12]$ if $a<1/2$, $C_+=[7/12,3/4]$ otherwise).
--
--   1. For every admissible mesh ($0<\eta_k\le1$, $\sum\eta_k=\infty$) and drift disturbances $\|\xi_k\|_\infty\le\varepsilon^2$: $Y,Y^s\in[11/48,37/48]$ at every index (17); all phase entries exist; and at the internal sections $j$ (every fourth phase entry, section $0$ at the start) the data $Y_j$ lie in the $j$-th alternating component, satisfy $P(Y_j)\le-119/256$ for $j\ge1$, and
--   $$|Y_j-c_j|\le2^{-j}|Y_0-c_0|+2d_s.\tag{18}$$
--   2. For every measurable forcing with $\|\xi(t)\|_\infty\le\varepsilon^2$ a.e., a solution from $z_0$ exists, and every solution has $Y(t),Y^s(t)\in[11/48,37/48]$ for all $t\ge0$, all its continuous phase entries, and the same three section statements at $\theta_{4j}$.
--
--   A degree-four assertion on the source, combined with the proved contract of cycles of the compiler, thus certifies an execution that branches forever, under every mesh and every forced flow.
--
--   **Formalization Note** $\Delta_\varepsilon$ is the published `deltaEps ε ε²`; sections are `kk (4j)` of the published `IsPhaseEntries` and $\theta_{4j}$ of `contPhaseEntry`. The constants $s_0$ and $B$ are chosen before $a$, the initial point, the mesh and the disturbance.
--
--   Differences from the source:
--   - reading: d_s = BΔε with B the constant of Theorem 14 for this program → an existential B > 0, chosen after K and before s, a, the initial point, the mesh and the disturbance; reason: Theorem 14's B is itself existential (published PolyEulerFlow.theorem_14)
--   - reading: at successive internal sections → sections 4j of the phase entries from index 0 (IsPhaseEntries) and θ_{4j} for the flow, existence of all phase entries asserted, section 0 at the start; reason: the base mission's section convention (Theorem 1: every fourth phase crossing of 9/10 after the initial section)
--   - reading: for every allowed mesh and forced flow → every admissible variable mesh with drift ≤ ε², and every measurable forcing ≤ ε² a.e., with existence of a forced solution and all solutions; reason: the meshes and forcings allowed in §5.3 (Proposition 21: every divergent variable mesh and every measurable forcing with this bound)
--   - encoding: the unchanged compiler (14) → the field (14) written out on the published CompiledState 1 1 with the published clockField; reason: it equals the published compiledField of program (13); the selector is Y/2 + (1 − v)/4
--   - encoding: Y(t), Y^s(t) ∈ [11/48, 37/48] ⊂ (1/5, 4/5) → Y, Y^s ∈ [11/48, 37/48]; reason: the inclusion into (1/5, 4/5) is arithmetic
--   - encoding: the certificate has degree four, and its list of coefficients has constant length → the identity P(Y) = 2304Y⁴ − 4608Y³ + 3296Y² − 992Y + 105 of (15); reason: the expansion exhibits the degree and the five coefficients
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 22 and (13)–(18), pp.22–23 (PDF 24–25); restated with proof pp.52–54 (PDF 54–56)

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_branchField
import Definitions.Def_PolyEulerFlow_IsUniformClock
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- **Theorem 22 (A compact certificate for an indefinitely branching execution)**, p.23 (PDF 25; restated pp.52–53, PDF 54–55).
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…): "Fix K ≥ 256. Initialize the unchanged
compiler (14) by p = (1, 0, 0, 0), τ_i = ε, Y = Y^s = a, v = (a − 1/2)/4, where a is any rational number in [5/16, 3/8] ∪ [5/8, 11/16].
Allow an initial error of sup norm at most ε²/16 in all eleven active coordinates, and drift disturbances of sup norm at most ε². For all
sufficiently large s, chosen independently of a, the quartic certificate and the contract of cycles imply, for every allowed mesh and forced
flow, Y(t), Y^s(t) ∈ [11/48, 37/48] ⊂ (1/5, 4/5) (t ≥ 0). (17) At successive internal sections, Y_j alternates between C₋ and C₊, and
P(Y_j) ≤ −119/256 for every j ≥ 1. If c_j alternates between 1/3 and 2/3, starting in the same component as a, then
|Y_j − c_j| ≤ 2^{−j}|Y_0 − c_0| + 2d_s, d_s = BΔ_ε ≤ 1/48. (18)"

**Formalization Note.** `ε = h^K`, `h = 2^{-s}`; `Δ_ε = (1 + log(1/ε))(ε^{1/4} + ε²)` is the published `deltaEps ε ε²`; `B > 0` and the
threshold `s₀` are existential and chosen before `a`, the initial point, the mesh and the disturbance. Internal sections are every fourth phase
entry: `kk (4j)` with the published `IsPhaseEntries` for executions, and `θ_{4j}` with the published `contPhaseEntry` for forced solutions,
whose phase entries are asserted to exist. The section `j = 0` is the start. The closing sentence "the certificate has degree four, and
its list of coefficients has constant length" is the first conjunct, the expansion (15) of the quartic into its five integer coefficients;
the disclaimer "we do not claim a small certificate on the full state" asserts nothing. -/
theorem theorem_22 (K : ℕ) (hK : 256 ≤ K) :
    (∀ Y : ℝ, quartic Y = 2304 * Y ^ 4 - 4608 * Y ^ 3 + 3296 * Y ^ 2 - 992 * Y + 105) ∧
    ∃ (s0 : ℕ) (B : ℝ), 0 < B ∧ ∀ s : ℕ, s0 ≤ s →
      let h : ℝ := scale s
      let ε : ℝ := h ^ K
      let ds : ℝ := B * deltaEps ε (ε ^ 2)
      let f : CompiledState 1 1 → CompiledState 1 1 := branchField K h
      let pv : Fin 4 → CompiledState 1 1 → ℝ := fun i w => phaseBit i w
      ds ≤ 1 / 48 ∧
      ∀ a : ℚ, ((a : ℝ) ∈ Set.Icc (5 / 16) (3 / 8) ∨ (a : ℝ) ∈ Set.Icc (5 / 8) (11 / 16)) →
        let c0 : ℝ := if (a : ℝ) < 1 / 2 then 1 / 3 else 2 / 3
        let cj : ℕ → ℝ := fun j => if Even j then c0 else 1 - c0
        let comp : ℕ → Set ℝ := fun j => if (Even j ↔ (a : ℝ) < 1 / 2) then Cminus else Cplus
        ∀ z0 : CompiledState 1 1, ‖z0 - branchInit K h a‖ ≤ ε ^ 2 / 16 →
          -- every admissible mesh and drift disturbance
          (∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState 1 1), IsAdmissibleMesh η → IsPermittedDisturbance (ε ^ 2) ξ →
            let z := eulerOrbit f z0 η ξ
            (∀ k, dataY (z k) 0 ∈ Set.Icc (11 / 48 : ℝ) (37 / 48) ∧ shadowY (z k) 0 ∈ Set.Icc (11 / 48 : ℝ) (37 / 48)) ∧
            ∃ kk : ℕ → ℕ, IsPhaseEntries pv z 0 kk ∧
              ∀ j : ℕ, dataY (z (kk (4 * j))) 0 ∈ comp j ∧
                (1 ≤ j → quartic (dataY (z (kk (4 * j))) 0) ≤ -119 / 256) ∧
                |dataY (z (kk (4 * j))) 0 - cj j| ≤ (2 : ℝ) ^ (-(j : ℤ)) * |dataY (z 0) 0 - c0| + 2 * ds) ∧
          -- every measurable forcing
          (∀ ξ : ℝ → CompiledState 1 1, IsPermittedForcing (ε ^ 2) ξ →
            (∃ z : ℝ → CompiledState 1 1, IsForcedSolution f z0 ξ z) ∧
            ∀ z : ℝ → CompiledState 1 1, IsForcedSolution f z0 ξ z →
              let θ := contPhaseEntry pv z
              (∀ t : ℝ, 0 ≤ t →
                dataY (z t) 0 ∈ Set.Icc (11 / 48 : ℝ) (37 / 48) ∧ shadowY (z t) 0 ∈ Set.Icc (11 / 48 : ℝ) (37 / 48)) ∧
              ContPhaseEntriesExist pv z ∧
              ∀ j : ℕ, dataY (z (θ (4 * j))) 0 ∈ comp j ∧
                (1 ≤ j → quartic (dataY (z (θ (4 * j))) 0) ≤ -119 / 256) ∧
                |dataY (z (θ (4 * j))) 0 - cj j| ≤ (2 : ℝ) ^ (-(j : ℤ)) * |dataY (z 0) 0 - c0| + 2 * ds) := by sorry

end PolyEulerFlow.Supplement
