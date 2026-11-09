-- Prove2me | Theorems.Thm_PolyContract_lemma_b_9
-- name    : PolyContract.lemma_b_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:00.233304+00:00
-- url     : https://prove2.me/theorems/b26489cc-0db0-4781-b92a-5d7a1cfb028a
-- title:
--   Lemma B.9 — embedding into a polymatroid
-- statement:
--   Let $\tilde f:2^E\to\mathbb R$ be submodular with $\tilde f(\emptyset)=0$, $a,b\in\mathbb R^E_{>0}$, $\Theta>0$, and
--   $$\Lambda\ge\max\Big\{0,\max_{S\subseteq E,\,e\in E\setminus S}\big(\tilde f(S)-\tilde f(S\cup\{e\})+\Theta b_e\big)/a_e\Big\}.$$
--   Then $f(S):=\tilde f(S)+\sum_{e\in S}(\Lambda a_e-\Theta b_e)$ is a rank function, and in the instance with $f$, $m_e:=a_e/b_e$ and $\beta_e:=1/b_e$, the level set $A_{\Theta-\theta}(\Lambda+\lambda)$ is the maximal minimizer of $\tilde f-\lambda a-\theta b$ for all $\lambda\ge-\Lambda$ and $\theta<\Theta$.
--
--   It turns a parametric minimization of a non-monotone submodular function into level sets of a best response.
--
--   Differences from the source:
--   - encoding: the level set A_{Θ−θ}(Λ + λ) of x⋆(Λ + λ) → the level set of every best response at the share Λ + λ; reason: the best response is unique (§3, p.7)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma B.9, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- **Lemma B.9** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.27). Let `f̃ : 2^E → ℝ` be submodular with `f̃(∅) = 0`, `a, b ∈ ℝ^E_{>0}`, `Θ > 0`
and `Λ ≥ max{0, max_{S ⊆ E, e ∈ E∖S} (f̃(S) − f̃(S ∪ {e}) + Θ b_e)/a_e}`. Then
`f(S) := f̃(S) + Σ_{e∈S}(Λ a_e − Θ b_e)` is a rank function, and in the instance with `f`,
`m_e := a_e/b_e` and `β_e := 1/b_e`, the level set `A_{Θ−θ}(Λ + λ)` is the maximal minimizer of
`f̃ − λa − θb` for all `λ ≥ −Λ` and `θ < Θ`.

**Formalization Note** The bound on `Λ` is `0 ≤ Λ` together with the bound for every pair
`S`, `e ∉ S`. `A_{Θ−θ}(Λ + λ)` is the level set at the best response at the share `Λ + λ ≥ 0`;
the statement is made for every best response (it is unique, §3 p.7). `λ` is written `lam`. -/
theorem lemma_b_9 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ft : Finset ι → ℝ) (a b : ι → ℝ) (Θ Λ : ℝ)
    (hft : NonmonotoneSubmod.Shared.Submodular ft) (hft0 : ft ∅ = 0)
    (ha : ∀ e, 0 < a e) (hb : ∀ e, 0 < b e) (hΘ : 0 < Θ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ (S : Finset ι) (e : ι), e ∉ S → (ft S - ft (insert e S) + Θ * b e) / a e ≤ Λ) :
    let I : QuadInstance ι :=
      ⟨fun S => ft S + ∑ e ∈ S, (Λ * a e - Θ * b e), fun e => a e / b e, fun e => 1 / b e⟩
    IsRankFunction I.f ∧
      ∀ lam θ : ℝ, -Λ ≤ lam → θ < Θ → ∀ x : ι → ℝ, I.IsBestResponse (Λ + lam) x →
        IsMaximalMinimizer (fun S => ft S - lam * setSum a S - θ * setSum b S)
          (I.levelSet (Λ + lam) x (Θ - θ)) := by sorry

end PolyContract
