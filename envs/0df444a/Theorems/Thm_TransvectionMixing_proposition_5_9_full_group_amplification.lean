-- Prove2me | Theorems.Thm_TransvectionMixing_proposition_5_9_full_group_amplification
-- name    : TransvectionMixing.proposition_5_9_full_group_amplification
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:57.474041+00:00
-- url     : https://prove2.me/theorems/8c9f3227-a28b-46ad-b0cf-c65d83c1ac91
-- title:
--   Proposition 5.9 — full-group amplification: both guarantees for $\mathcal S=[n]\times[n]$ from time $\lceil 187n^2+13n\log(1/\varepsilon)\rceil$
-- statement:
--   Let $n\ge 256$ and $q\ge Q_{\mathrm{all}}(n)=(5000n)^{6n^2}$. For every $0<\varepsilon<1$ and every integer $t\ge\lceil 187n^2+13n\log(1/\varepsilon)\rceil$, both guarantees of (3) hold for $\mathcal S=[n]\times[n]$:
--   $$
--   d_{[n]\times[n]}(t)\le\varepsilon,\qquad \sup_X\Pr_{\sigma:|\sigma|=t}\bigl[d^\sigma_{[n]\times[n]}(X)>\varepsilon\bigr]\le\varepsilon .
--   $$
--
--   This covers the very-small-error regime with the single field threshold $Q_{\mathrm{all}}$.
--
--   Differences from the source:
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
--   - encoding: every integer time at least ⌈187n² + 13n log(1/ε)⌉ → every t : ℕ with ⌈187n² + 13n log(1/ε)⌉₊ ≤ t; reason: same times
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Proposition 5.9, p.30

import Mathlib
import Definitions.Def_TransvectionMixing_dS
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

/-- **Proposition 5.9** (full-group amplification) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.4, p.30). For `n ≥ 256` and
`q ≥ Q_all(n)`, both guarantees in (3) hold for `𝒮 = [n] × [n]`,
`d_𝒮(t) ≤ ε` and `sup_X Pr_{σ:|σ|=t}[d^σ_𝒮(X) > ε] ≤ ε`, at every integer time
`t ≥ ⌈187n² + 13n log(1/ε)⌉`, for `0 < ε < 1`. -/
theorem proposition_5_9_full_group_amplification (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (n : ℕ) (hn : 256 ≤ n) (hq : Qall n ≤ Fintype.card F) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℕ)
    (ht : ⌈187 * (n : ℝ) ^ 2 + 13 * n * Real.log (1 / ε)⌉₊ ≤ t) :
    dS F (Finset.univ : Finset (Fin n × Fin n)) t ≤ ε ∧
      (⨆ X : Matrix.SpecialLinearGroup (Fin n) F, skelBadProb F Finset.univ t X ε) ≤ ε := by sorry

end TransvectionMixing
