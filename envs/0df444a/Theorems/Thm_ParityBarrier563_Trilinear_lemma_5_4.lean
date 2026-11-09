-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_5_4
-- name    : ParityBarrier563.Trilinear.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:32.25446+00:00
-- url     : https://prove2.me/theorems/d9b01ef5-0516-45e8-9240-e84a5f4257db
-- title:
--   Lemma 5.4 — the u-th moment of the correlation of a restricted random slice is at most 2^{−u|T_x|/4}+2^{−u|T_y|/4}
-- statement:
--   Let $u\ge2$ be even, and let $\rho$ be a restriction of the $2n$ data variables $x,y$ such that $|T_x|\ge2u$ and every set $A\subseteq\{0,\dots,n-1\}$ with $|A|\le u$ satisfies $|A+T_y|\ge|A|\,|T_y|/2$. Let $J:\{0,1\}^{\mathrm{live}(\rho)}\to[-1,1]$ be any function. If $a$ is uniform in $\{0,1\}^{2n-1}$ and $g^a=2f^a_n-1$ is the sign of the slice $f^a_n$, then
--
--   $$\mathbb E_a\Bigl[\Bigl(\mathbb E_z\bigl[g^a_\rho(z)\,J(z)\bigr]\Bigr)^u\Bigr]\le2^{-u|T_x|/4}+2^{-u|T_y|/4},$$
--
--   where $z$ is uniform in $\{0,1\}^{\mathrm{live}(\rho)}$.
--
--   With Markov's inequality this bounds, for each fixed test $J$, the probability over the seed that a restricted slice correlates with $J$.
--
--   Differences from the source:
--   - encoding: T_x, T_y ⊆ {0,…,n−1} and the sumset A + T_y → sets of natural numbers and the pointwise sum of finite sets of natural numbers; reason: ordinary integer sumsets; no wraparound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 5.4, printed p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction
open scoped Pointwise

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 5.4, printed p.17 / PDF 19. -/
theorem lemma_5_4 (n u : ℕ) (ρ : Restriction (SliceVar n)) (J : (Live ρ → Bool) → ℝ)
    (hu : 2 ≤ u) (hev : Even u) (hTx : 2 * u ≤ (liveX ρ).card)
    (hTy : ∀ A ∈ (Finset.range n).powerset, A.card ≤ u →
      (A.card : ℝ) * (liveY ρ).card / 2 ≤ ((A + liveY ρ).card : ℝ))
    (hJ : ∀ z, J z ∈ Set.Icc (-1 : ℝ) 1) :
    avg (fun a : Fin (2 * n - 1) → Bool =>
        (avg (fun z => restrict ρ (sgn (slice n a)) z * J z)) ^ u) ≤
      (2 : ℝ) ^ (-((u : ℝ) * (liveX ρ).card / 4)) +
        (2 : ℝ) ^ (-((u : ℝ) * (liveY ρ).card / 4)) := by sorry

end ParityBarrier563.Trilinear
