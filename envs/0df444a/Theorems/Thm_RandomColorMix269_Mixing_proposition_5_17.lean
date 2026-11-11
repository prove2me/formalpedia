-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_proposition_5_17
-- name    : RandomColorMix269.Mixing.proposition_5_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:37.926241+00:00
-- url     : https://prove2.me/theorems/a63a31d8-3a2b-4711-9660-6d7aedaa1ede
-- title:
--   Proposition 5.17 — every pinned block $B_u$ is connected and relaxes in time $\le q^{2(1+DK_1)\ln n+1}$
-- statement:
--   Fix $\eta\in(0,1)$; there is $d_0>1$ such that for every $d\ge d_0$, every integer $q\ge(1+\eta)d$ and every $K_1>0$, for all sufficiently large $n$ the following holds for every graph $G$ on $[n]$ on the event of Lemma 5.10 (every component of $G[S]$ is a tree or unicyclic with at most $K_1\ln n$ vertices). For every block $B_u=S\cup\{u\}$, $u\in U$, and every feasible outside pinning $\tau$ on $V\setminus B_u$, the support of $\mu^\tau_{G,q}$ is connected under single-site recolourings, and the continuous-time single-site Glauber dynamics of $\mu^\tau_{G,q}$ on $B_u$ has
--   $$
--   T_{\mathrm{rel}}\le q^{2(1+DK_1)\ln n+1}.
--   $$
--   These are the local relaxation bounds $R$ required by the comparison Lemma 5.2.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: spectral gap as an infimum over Var>0 and T_rel = 1/λ_gap with 1/0 = ∞ → infimum in ℝ≥0∞ (⊤ when no function has positive variance) and its inverse in ℝ≥0∞; reason: the source's convention; it avoids a real infimum of an empty set and a real inverse of 0
--   - generalization: K₁ the constant of Lemma 5.10 → every K₁ > 0; reason: the proof uses only the event with constant K₁; it specializes to Lemma 5.10's K₁
--   - encoding: continuous-time single-site dynamics of µ^τ on B_u → rate-one single-site dynamics of the pinned law on all of V; reason: pinned sites have zero conditional variance, so only sites of B_u contribute
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.37–38, Proposition 5.17

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Proposition 5.17, p.37: simultaneous in every block and feasible outside
pinning, under precisely the buffered geometry event of Lemma 5.10. -/
theorem proposition_5_17 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      ∀ q : ℕ, (1 + η) * d ≤ q → ∀ K₁ : ℝ, 0 < K₁ →
        ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
          BufferEvent G (cutoff η d) K₁ →
            ∀ (u : lowRegion G (cutoff η d)) (x : Fin n → Fin q),
              Feasible (MarkovMixing.properColoringDist G q) (bufferBlocks G (cutoff η d) u)ᶜ x →
              let μτ := SpinGirth5.pin (MarkovMixing.properColoringDist G q)
                (bufferBlocks G (cutoff η d) u)ᶜ x
              SupportConnected μτ ∧ singleRelaxation μτ ≤
                ENNReal.ofReal ((q : ℝ) ^ (2 * (1 + cutoff η d * K₁) * Real.log n + 1)) := by sorry

end RandomColorMix269.Mixing
