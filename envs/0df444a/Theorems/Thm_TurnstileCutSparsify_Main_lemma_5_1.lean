-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_5_1
-- name    : TurnstileCutSparsify.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:29.221935+00:00
-- url     : https://prove2.me/theorems/7169ae2a-5e53-455c-9c13-514c3b5183b5
-- title:
--   Lemma 5.1 — conditional estimation bound for Rademacher quadratic forms with sign separation (18), uniform over a family of sets
-- statement:
--   Let the evaluation signs $\sigma^{\pi,l}_f$, indexed by a pair $f\in[N]$, a layer and row $\pi$, and a repetition $l\in[R]$ ($R\ge1$), be independent Rademacher signs, and let all other quantities be fixed. Let $T\subseteq[N]$ be a set of targets; target $e$ is decoded at $\pi_e$, with decoding signs $\sigma^{\pi_e,l}_e$, and has a collision vector $u_e\in\mathbb R^N$. Assume
--   $$u_e(f)=0\quad\text{for all }e,f\in T\text{ with }\pi_e=\pi_f.\qquad(18)$$
--   With $c_{e,l}=\sum_fu_e(f)\sigma^{\pi_e,l}_f$ and $Q_F=\frac1R\sum_{e\in F\cap T}\sum_{l=1}^R\sigma^{\pi_e,l}_ec_{e,l}$, let $\mathcal P$ be a family of subsets of $[N]$ and, for $F\in\mathcal P$, $\ell_F>0$ and $v_F\ge\sum_{e\in F\cap T}\|u_e\|_2^2$. Then
--   $$\mathbb P\Big(\exists F\in\mathcal P:\ |Q_F|>\sqrt{18v_F\ell_F/R}\Big)\le|T|e^{-R}+2\sum_{F\in\mathcal P}e^{-\ell_F}.\qquad(19)$$
--
--   Differences from the source:
--   - generalization: labels π = layer–row pairs → labels from an arbitrary finite type Λ; reason: the proof (p. 20) uses only that the label set is finite; layer–row pairs are an instance
--   - encoding: pairs f ∈ [N]; independent Rademacher signs; collision vectors u_e ∈ ℝ^N; a family P of subsets → Fin N; σ uniform on Λ → Fin R → Fin N → Bool (true = −1); u : Fin N → Fin N → ℝ; Fam : Finset (Finset (Fin N)); errQ, collNoise; reason: same objects; P is finite as a family of subsets of a finite set
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 5.1, p. 19

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Randomness

open scoped BigOperators Classical

namespace TurnstileCutSparsify.Main

/-- **Lemma 5.1** (Conditional estimation bound; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 19).
Let the evaluation signs `σ^{π,l}_f` (a pair `f ∈ [N]`, a label `π` of a finite label set, a
repetition `l ∈ [R]`) be independent Rademacher signs, and let all other quantities be fixed. Let
`T ⊆ [N]` be the targets; target `e` is decoded at label `π_e` and has collision vector `u_e`.
Assume (18): `u_e(f) = 0` for all `e, f ∈ T` with `π_e = π_f`. With
`c_{e,l} = Σ_f u_e(f) σ^{π_e,l}_f` and `Q_F = (1/R) Σ_{e ∈ F ∩ T} Σ_l σ^{π_e,l}_e c_{e,l}`, let `Fam` be a
family of subsets of `[N]` and, for `F ∈ Fam`, `ℓ_F > 0` and `v_F ≥ Σ_{e ∈ F ∩ T} ‖u_e‖₂²`. Then
`P(∃ F ∈ Fam : |Q_F| > √(18 v_F ℓ_F / R)) ≤ |T| e^{−R} + 2 Σ_{F ∈ Fam} e^{−ℓ_F}` (19). -/
theorem lemma_5_1 {N R : ℕ} {Λ : Type} [Fintype Λ] (hR : 1 ≤ R) (T : Finset (Fin N))
    (π : Fin N → Λ) (u : Fin N → Fin N → ℝ)
    (h18 : ∀ e ∈ T, ∀ f ∈ T, π e = π f → u e f = 0)
    (Fam : Finset (Finset (Fin N))) (ℓF vF : Finset (Fin N) → ℝ) (hℓ : ∀ F ∈ Fam, 0 < ℓF F)
    (hv : ∀ F ∈ Fam, ∑ e ∈ F ∩ T, ∑ f, u e f ^ 2 ≤ vF F) :
    prob (fun σ : Λ → Fin R → Fin N → Bool =>
        ∃ F ∈ Fam, Real.sqrt (18 * vF F * ℓF F / R) < |errQ π u σ T F|) ≤
      (T.card : ℝ) * Real.exp (-(R : ℝ)) + 2 * ∑ F ∈ Fam, Real.exp (-ℓF F) := by sorry

end TurnstileCutSparsify.Main
