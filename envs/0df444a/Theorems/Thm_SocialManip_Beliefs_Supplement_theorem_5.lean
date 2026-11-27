-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_5
-- name    : SocialManip.Beliefs.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:17:45.739194+00:00
-- url     : https://prove2.me/theorems/ef65c145-359a-4b48-8187-dc75bda3c7d5
-- title:
--   Theorem 5, p. 25 (corrected: refutation) — no cutoff on the full contiguous-block domain
-- statement:
--   Printed Theorem 5 permits a contiguous Bayesian block without requiring its size or the complementary DeGroot block to grow regularly. For each network size $n$, put all agents except agent $0$ in $B_n$ when $n$ is even, and put only agent $0$ in $B_n$ when $n$ is odd. These are contiguous blocks for every positive $n$. Use the printed ring–complete mixture with parameter $\eta\in[0,1]$, all qualities $3/4$, prior $1/2$, rates $\lambda=\lambda^*=1$, cost $\varepsilon=1/4$, and $b=1/2$. Then
--   $$\nexists\eta^*\in\mathbb R:\quad
--   \begin{cases}
--   \eta<\eta^*\ \Longrightarrow\ k\to+\infty\text{ in probability conditional on }y=S,\\
--   \eta>\eta^*\ \Longrightarrow\ \text{every network in the family is impervious}.
--   \end{cases}$$
--   The growth assertion has the full quantifiers: every fixed count threshold, all sufficiently large sizes, and all long-horizon equilibria. Even sizes have at most one manipulable agent. At size three and $\eta=1$, the single-Bayesian complete network is susceptible. These two facts rule out every real cutoff, including a cutoff outside $[0,1]$.
--
--   This is a refutation of the conjunction of the printed conclusions on its allowed contiguous-block domain, not a replacement phase transition with additional growth or cost premises. The empty network is an irrelevant totalized value of the family at $n=0$.
--
--   Differences from the source:
--   - correction: a cutoff exists for every permitted contiguous-block family → an explicit permitted alternating family admits no cutoff at all; reason: even sizes obstruct the lower branch for every positive cutoff; the complete three-agent member obstructs the upper branch for every nonpositive cutoff
--   - reading: growth in the number manipulated in the misinformation regime → conditional count law in state S; reason: the source proof pp. 51–52 studies misinformation in that fixed state
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 5, p. 25; ring p. 21; (3) p. 23; G_η p. 25; Example 3 p. 37; proof pp. 51–52

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open Filter Topology

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The printed chain alternative allows the Bayesian block size to vary with n. Even n
leave one DeGroot, odd n have one Bayesian. No single cutoff can satisfy the two conclusions,
even if η* is allowed outside [0,1]. This refutes the complete printed family-level claim. -/
theorem theorem_5 :
    let Bf : ∀ n : ℕ, Finset (Fin n) := fun n =>
      if Even n then Finset.univ.filter (fun i : Fin n => i.val ≠ 0) else Finset.univ.filter (fun i : Fin n => i.val = 0)
    let Mf : ∀ n : ℕ, ℝ → Model n := fun n η =>
      ⟨Bf n, etaTheta n η, etaAlpha n η, (fun _ => 3 / 4), 1 / 2, 1, 1, 1 / 4, 1 / 2⟩
    (∀ n, IsRingArc (Bf n)) ∧
      ¬ ∃ ηstar : ℝ,
        (∀ η ∈ Set.Icc (0 : ℝ) 1, η < ηstar → ∀ K : ℕ, ∃ N : ℕ, ∀ n, N ≤ n →
          ManipulatesAtLeast (Mf n η) K) ∧
        (∀ η ∈ Set.Icc (0 : ℝ) 1, ηstar < η → ∀ n, Impervious (Mf n η)) := by sorry

end SocialManip.Beliefs.Supplement
