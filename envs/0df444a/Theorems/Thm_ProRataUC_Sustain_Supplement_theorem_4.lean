-- Prove2me | Theorems.Thm_ProRataUC_Sustain_Supplement_theorem_4
-- name    : ProRataUC.Sustain.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:24:34.206992+00:00
-- url     : https://prove2.me/theorems/e4d1e3f8-5d6a-4694-a39c-a8100277209b
-- title:
--   Theorem 4, p. 62 — if every π2j/π1j ≤ λ1/(q2λ2), the core of the coalition value f is non-empty
-- statement:
--   This is Theorem 4 of Alaei, Makhdoumi, Malekian and Pekeč (Appendix B.1.4).
--
--   Consider a streaming platform with a finite, nonempty set $\mathcal M$ of artists and two user types $i\in\{1,2\}$ with usage rates $\lambda_2>\lambda_1>0$, population masses $q_1,q_2\in(0,1)$ with $q_1+q_2=1$, and listening probabilities $\pi_{ij}\ge0$ with $\sum_{j\in\mathcal M}\pi_{ij}=1$ for $i=1,2$; assume $\pi_{1j}>0$ for every artist $j$. For a coalition $J\subseteq\mathcal M$ let
--   $$f(J)=\max_{S\subseteq\{1,2\}}\Big(\min_{i\in S}\lambda_i\sum_{j\in J}\pi_{ij}\Big)\Big(\sum_{i\in S}q_i\Big)$$
--   be the largest total subscription fee $J$ collects on a competing platform. If
--   $$\max_{j\in\mathcal M}\frac{\pi_{2j}}{\pi_{1j}}\le\frac{\lambda_1}{q_2\lambda_2},$$
--   then the core of $f$ is non-empty: there is a real vector $(x_j)_{j\in\mathcal M}$ with $f(J)\le\sum_{j\in J}x_j$ for every $J\subseteq\mathcal M$ and $f(\mathcal M)=\sum_{j\in\mathcal M}x_j$.
--
--   The result says that when no artist is much more popular with heavy (type 2) users than with light (type 1) users, the platform offering all artists can pay them so that no coalition of artists is better off forming a competing platform; its monopoly is then sustainable under a suitable payment rule.
--
--   **Formalization Note** The ratio $\pi_{2j}/\pi_{1j}$ presupposes $\pi_{1j}>0$, which is stated as the hypothesis `hpos`. Without it Lean's convention $x/0=0$ would make the statement false: with two artists, $\pi_1=(1,0)$, $\pi_2=(0,1)$, both Lean ratios are $0$, but a core vector would need $x_1\ge q_1\lambda_1$, $x_2\ge q_2\lambda_2$ and $x_1+x_2=\lambda_1<q_1\lambda_1+q_2\lambda_2$. The maximum over artists is `Finset.univ.sup'`, which needs $\mathcal M$ nonempty; that already follows from $\sum_j\pi_{1j}=1$. Only the sufficient direction stated in Theorem 4 is formalized. Assumption 1 ($\lambda_1\ge\lambda_2q_2$) is not assumed; it follows from the hypothesis.
--
--   Differences from the source:
--   - encoding: the ratio π2j/π1j, defined only when π1j > 0 → the hypothesis hpos : ∀ j, 0 < π1j stated explicitly; reason: Lean's real division returns 0 at π1j = 0, and the paper's ratio is undefined there, so hpos excludes only the cases in which the hypothesis is undefined.
--   - encoding: max over the artists j ∈ M → Finset.univ.sup' with [Nonempty M]; reason: M is nonempty because Σ_j π1j = 1 in the standing assumptions, so no instance changes.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 62, App. B.1.4, Theorem 4

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting
import Definitions.Def_ProRataUC_Sustain_Supplement_CoalitionValue
import Definitions.Def_ProRataUC_Sustain_Supplement_Core

namespace ProRataUC.Sustain.Supplement

open ProRataUC.Sustain

/-- Theorem 4, p. 62: if `max_{j∈M} π2j/π1j ≤ λ1/(q2 λ2)`, the core of the coalition value `f`
is non-empty. The ratio presupposes `π1j > 0` for every artist (`hpos`). -/
theorem theorem_4 {M : Type*} [Fintype M] [Nonempty M] (s : Setting M) (hs : s.Standing)
    (hpos : ∀ j, 0 < s.pi1 j)
    (h : Finset.univ.sup' Finset.univ_nonempty (fun j => s.pi2 j / s.pi1 j) ≤
      s.lam1 / (s.q2 * s.lam2)) :
    ∃ x : M → ℝ, InCore s x := by sorry

end ProRataUC.Sustain.Supplement
