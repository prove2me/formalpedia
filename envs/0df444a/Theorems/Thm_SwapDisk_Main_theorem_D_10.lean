-- Prove2me | Theorems.Thm_SwapDisk_Main_theorem_D_10
-- name    : SwapDisk.Main.theorem_D_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:50.505359+00:00
-- url     : https://prove2.me/theorems/6db98582-093c-4425-bf77-2500936bb7b9
-- title:
--   Theorem D.10 — ex ante dictionary obstruction: against $D_{\mathrm{dir}}$ every dictionary learner has $\mathbb ER_T\ge1+(T-1)\beta_N\ge T\beta_N\ge 2T/(3N^2)$
-- statement:
--   Let $T\ge2$, $N\ge1$, and let $D_{\mathrm{dir}}$ draw $\omega$ uniform on $S^1$, independently of the learner, and play $g_t=-\omega$ in every round. Every admissible learner whose actions lie in an ex ante dictionary of at most $N$ physical points (privately randomized dictionaries included, repetitions allowed in their initial encoding) satisfies
--   $$\mathbb E_{A,D_{\mathrm{dir}}}R_T\ge1+(T-1)\beta_N\ge T\beta_N\ge\frac{2T}{3N^2}.$$
--   For every such learner there is a deterministic $u\in S^1$ whose constant losses $-u$ give expected regret at least $1+(T-1)\beta_N$.
--
--   This is the $T/N^2$ half of the fixed-dictionary lower bound.
--
--   Differences from the source:
--   - encoding: the online protocol of Eq. (A.11) with standard Borel private states and the Borel σ-field of the weak topology on P(B²₂) → `Learner`/`Adversary`/`law` of the Protocol definition: Giry σ-field on `ProbabilityMeasure Disk`, rounds indexed from 0, one kernel per `t : ℕ` (those with t ≥ T unused), private states standard Borel types; reason: the Giry and weak-topology Borel σ-fields coincide on the Polish space B²₂; the other changes are index conventions; same learners, adversaries and laws
--   - encoding: E[·] and P{·} under the canonical law → Bochner integrals and measures of events under `law`/`sharpLaw` (`ENNReal.ofReal p ≤ μ {…}` for P{…} ≥ p); reason: the integrands are bounded Borel functions (Proposition A.1); same values
--   - encoding: D_dir: ω uniform on S¹ drawn once, g_t = −ω → `Ddir`: initial state θ ∼ dθ/2π on [0, 2π), deterministic kernels playing −(cos θ, sin θ) and keeping θ; reason: (cos θ, sin θ) has law σ
--   - encoding: actions in an ex ante dictionary of at most N physical points → `IsDictLearner T N L`; reason: §A.5's encoding: a Borel N-tuple of the initial state containing every played point a.s.
--   - encoding: constant losses −u for a deterministic u ∈ S¹ → `constAdversary (negDisk u)` with `u ∈ unitCircle`; reason: same adversary
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 48, Theorem D.10

import Mathlib
import Definitions.Def_SwapDisk_Main_Protocol

namespace SwapDisk.Main

/-- Theorem D.10 (Ex ante dictionary obstruction), p. 48: every admissible learner whose actions
lie in an ex ante (possibly privately randomized) dictionary of at most `N` points has
`E_{A,D_dir} R_T ≥ 1 + (T − 1)β_N ≥ Tβ_N ≥ 2T/(3N²)`, and some deterministic `u ∈ S¹` whose
constant losses `−u` give expected regret at least `1 + (T − 1)β_N`. -/
theorem theorem_D_10 (T N : ℕ) (hT : 2 ≤ T) (hN : 1 ≤ N) (L : Learner)
    (hL : IsDictLearner T N L) :
    1 + ((T : ℝ) - 1) * betaN N ≤ expectedRegret T L Ddir ∧
    (T : ℝ) * betaN N ≤ 1 + ((T : ℝ) - 1) * betaN N ∧
    2 * (T : ℝ) / (3 * (N : ℝ) ^ 2) ≤ (T : ℝ) * betaN N ∧
    ∃ u : Disk, (u : E2) ∈ unitCircle ∧
      1 + ((T : ℝ) - 1) * betaN N ≤ expectedRegret T L (constAdversary (negDisk u)) := by sorry

end SwapDisk.Main
