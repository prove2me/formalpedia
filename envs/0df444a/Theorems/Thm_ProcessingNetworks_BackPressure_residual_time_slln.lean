-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_residual_time_slln
-- name    : ProcessingNetworks.BackPressure.residual_time_slln
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:02:42.360986+00:00
-- url     : https://prove2.me/theorems/5c15bedb-5916-42b2-af74-ace405d6ef4c
-- title:
--   Lemma 9.14 — a residual-time SLLN (milestone)
-- statement:
--   **Lemma 9.14.** Let $\hat v_j(t)$ be the residual (or next) type-$j$ service time at $t$, and
--   $u_i(t)$ the residual inter-arrival time for class $i$. For a sample path satisfying the SLLNs
--   (2.14)-(2.15), the negligibility condition (6.38), and its inter-arrival analogue (9.44),
--   $\hat v_j(t)/t \to 0$ and $u_i(t)/t \to 0$ as $t \to \infty$.
--
--   This supplies the vanishing-remainder estimate Theorem 9.13's proof needs when a server
--   becomes idle or completes a service just before a would-be-preferred allocation becomes
--   available — the mechanism specific to single-server, one-at-a-time basic back-pressure that
--   Theorem 9.12's relaxed-model proof does not need.
--
--   **Formalization note.** The book's own proof bounds $\hat v_j(t)$ by
--   $\max_{0\le\ell\le S_j(t)+1} v_j(\ell)$ (via the completion-count process $S_j$, with
--   $S_j(t)/t \to 1/m_j$ by the SLLN) and argues (9.56) "follows from (9.44)" analogously via an
--   arrival-count process; this mission states both bounding relationships and the corresponding
--   count-process SLLNs as explicit hypotheses, matching the proof's actual structure. (9.44)
--   itself reads, verbatim (p. 178, PDF p. 194, in Theorem 9.13's preparatory material rather than
--   in the excerpt `BRIEF.md` quoted for this lemma): "$\lim_{n\to\infty} \frac1n
--   \max_{1\le\ell\le n} u_i(\ell) = 0$ for each $i\in\mathcal I$" — confirmed by reading
--   `source.txt` directly, matching `h944` exactly (flagged as confirmed, not reconstructed, in
--   `MODERATION_NOTES.md`). The book's own text prints (9.56)'s left side as `u_i(s,ω)`,
--   inconsistent with every other use of `t` in the surrounding proof; `t` is used here as
--   evidently intended, per `BRIEF.md`'s own note.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 181, Lemma 9.14

import Mathlib

namespace ProcessingNetworks.BackPressure

open Filter

/-- Lemma 9.14, Dai & Harrison p. 181 (PDF p. 197): let `v̂_j(t)` be the residual service time of
the type-`j` service underway at `t` (or, if none, the service time of the next type-`j` service
to start after `t`), and `u_i(t)` the residual inter-arrival time for class `i` at `t`. For a
sample path satisfying the SLLNs (2.14)/(2.15), the negligibility condition (6.38), and its
inter-arrival analogue (9.44), `v̂_j(t)/t → 0` and `u_i(t)/t → 0` as `t → ∞`. Formalized via the
bounding relationship the book's own proof uses (`v̂_j(t) ≤ max_{0≤ℓ≤S_j(t)+1} v_j(ℓ)` and the
analogous bound for `u_i` via an arrival-count process `N_i`), together with the SLLNs for the
completion/arrival-count processes `S_j(t)/t → 1/m_j`, `N_i(t)/t → 1/m'_i` that (2.15)/(9.44)
supply. -/
theorem residual_time_slln
    {J I : ℕ} (v : Fin J → ℕ → ℝ) (m : Fin J → ℝ) (interArr : Fin I → ℕ → ℝ) (mInter : Fin I → ℝ)
    (vhat : Fin J → ℝ → ℝ) (uhat : Fin I → ℝ → ℝ) (S : Fin J → ℝ → ℕ) (N : Fin I → ℝ → ℕ)
    (h215v : ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ) / n) atTop (nhds (m j)))
    (h215u :
      ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, interArr i ℓ) / n) atTop (nhds (mInter i)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j (ℓ + 1)) atTop (nhds 0))
    (h944 :
      ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, interArr i (ℓ + 1)) atTop
        (nhds 0))
    (hvhat : ∀ j t, 0 ≤ t → vhat j t ≤ ⨆ ℓ ∈ Finset.Icc 0 (S j t + 1), v j ℓ)
    (huhat : ∀ i t, 0 ≤ t → uhat i t ≤ ⨆ ℓ ∈ Finset.Icc 0 (N i t + 1), interArr i ℓ)
    (hS : ∀ j, Tendsto (fun t : ℝ => (S j t : ℝ) / t) atTop (nhds (m j)⁻¹))
    (hN : ∀ i, Tendsto (fun t : ℝ => (N i t : ℝ) / t) atTop (nhds (mInter i)⁻¹)) :
    (∀ j, Tendsto (fun t => vhat j t / t) atTop (nhds 0)) ∧
    (∀ i, Tendsto (fun t => uhat i t / t) atTop (nhds 0)) := by sorry

end ProcessingNetworks.BackPressure
