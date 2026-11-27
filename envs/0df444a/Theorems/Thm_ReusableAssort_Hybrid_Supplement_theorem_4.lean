-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_Supplement_theorem_4
-- name    : ReusableAssort.Hybrid.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:19:54.937436+00:00
-- url     : https://prove2.me/theorems/feffc398-bbc1-45f2-916c-1c890055d1aa
-- title:
--   Theorem 4, p. 20 — Sim+Hybrid(ii) is (1 − min{1/2, ε*(c_min)})-competitive against Expected-LP
-- statement:
--   Let the instance satisfy the model assumptions, let $y^*$ be an optimal solution of Expected-LP$[\{F_t\}_{t=1}^T]$ with $\sum_{S\in\mathcal S} y^*_{S,t,z} = 1$ for all $t, z$, and let $\gamma$ be a minimizer $\gamma^*(c_{\min})$ of (1) at $c_{\min} = \min_i c_i$. Then for every tie-break rule, Sim+Hybrid(ii) — which at each time runs whichever of Algorithm 2 (with $\gamma$) and Algorithm 3 has the higher expected revenue-to-go from the current state — earns
--   $$\mathbb E[\mathrm{Rev}_{\mathrm{H(ii)}}] \ge \Bigl(1 - \min\bigl\{\tfrac12, \varepsilon^*(c_{\min})\bigr\}\Bigr)\,\mathrm{LP}(y^*).$$
--
--   From every valid time and outstanding-return state, including the terminal time $T+1$, its conditional expected revenue also dominates that of each component algorithm started in that same state.
--
--   This is a companion theorem to the mission's goal (Theorem 3, for Sim+Hybrid(i)); it is not used in that proof. It gives the same guarantee for the variant the paper uses in its simulations.
--
--   **Formalization Note** The switch uses exact conditional expectations; see the list below.
--
--   Differences from the source:
--   - reading: Sim+Hybrid(ii) switches on Monte-Carlo estimates of the expected future revenues of Algorithms 2 and 3 → the switch compares the exact conditional expected revenues from t to T, started at time t in the current state J (base expRev with start time t and outstanding returns J); reason: the proof sketch (pp. 20–21) treats the comparison as exact ('Suppose Monte-Carlo simulation suggests that given state J, Algorithm 2 achieves higher expected revenue'); no sample size or error is given, and with estimation error no bound is proved
--   - reading: state J: on-hand units and the return time of each allocated unit; ties not specified → J = retState (units out per product and return time, from which the on-hand units follow); the theorem holds for every tie-break function tb of (t, J); reason: the proof sketch's state; quantifying over tie-breaks covers every reading of the unspecified tie rule
--   - reading: Algorithm 2 inside Sim+Hybrid(ii), discard probability not restated → random discarding with γ, for every minimizer γ = γ*(c_min) of (1); reason: the hybrid inherits Theorem 1's algorithm, which uses γ*(c_min)
--   - reading: the model of §2.1 (types ⟨ϕ^z, r^z, G^z⟩, Assumptions 1–2, c_i ∈ ℤ₊, durations g^z_i on [T]) → the published base Instance.Assumptions: one finite type space, durations on {1, …, T}, ϕ^z(S, ·) a sub-probability on S, weak substitutability on 𝒮, 𝒮 nonempty and downward closed, r ≥ 0, c_i ≥ 1; reason: these are the base mission's disclosed readings of the model, reused unchanged by reference
--   - encoding: competitive ratio α against Expected-LP (Definition 1) → α · lpObj I y ≤ expected revenue, for every optimal y with Σ_S y_{S,t,z} = 1; reason: the paper's ratio without dividing by a possibly zero LP value, as in Theorems 1–3 of the base mission; p. 11 takes the optimal assignment normalized without loss of generality
--   - generalization: The proof sketch compares both component policies from any current time t and state J. → The conclusion also states this domination for every ValidStart at t in {1,...,T+1}; at T+1 all revenues are zero.; reason: This restores the separate statewise claim retained in the source map; the terminal extension is the empty run.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 20, Theorem 4 (proof sketch pp. 20–21)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_HybridII

namespace ReusableAssort.Hybrid.Supplement

theorem theorem_4 {n T : ℕ} [NeZero n] {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPOptimal I y) (hN : Normalized I y)
    (γ : ℝ) (hγ : IsGammaStar (cmin I : ℝ) γ)
    (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) :
    (1 - min (1 / 2) (epsStar (cmin I : ℝ))) * lpObj I y ≤ expRevHybridII I y γ tb ∧
    ∀ t ∈ Finset.Icc 1 (T + 1), ∀ J, ValidStart I t J →
      max (expRev I y (alg2 γ) t J) (expRev I y (alg3 I y) t J) ≤
        expRevHybridIIFrom I y γ tb t J := by sorry

end ReusableAssort.Hybrid.Supplement
