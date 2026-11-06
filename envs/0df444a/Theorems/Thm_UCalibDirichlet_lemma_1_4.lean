-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_1_4
-- name    : UCalibDirichlet.lemma_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:38.964638+00:00
-- url     : https://prove2.me/theorems/0ebb3861-a262-4867-829a-78c495e741ae
-- title:
--   Lemma 1.4 — regret decomposition of Algorithm 1
-- statement:
--   Let $\ell_F$ be a proper loss with finite convex potential $F$, let $T\ge1$ and fix outcomes $i_1,\dots,i_T$, with counts $N_T$, empirical distribution $\hat p_T=N_T/T$ and Algorithm 1's parameters $a_t=N_{t-1}+\mathbf 1$. The regret of Algorithm 1 decomposes as
--   $$\mathrm{Reg}_F(T)=\underbrace{\Lambda_F(\mathbf 1)-\Lambda_F(N_T+\mathbf 1)+TF(\hat p_T)}_{\text{BTPL regret}}+\underbrace{\sum_{t=1}^T\delta^{i_t}_F(a_t)}_{\text{stability}},$$
--   where $\delta^i_F(a)=\mathbb E_{P\sim\mathrm{Dir}(a)}[\ell_F(P,i)]-\mathbb E_{P\sim\mathrm{Dir}(a+e_i)}[\ell_F(P,i)]$.
--
--   The BTPL term is the penalty of the hallucinated outcomes; the stability term compares the forecasts of follow and be the perturbed leader. The two are bounded separately (Lemmas 1.5, 1.6).
--
--   Differences from the source:
--   - encoding: proper loss ℓ_F : Δ_K × [K] → ℝ ∪ {+∞} with finite convex potential F → ℓ : (Fin K → ℝ) → Fin K → EReal with IsProperLoss ℓ and HasFiniteBayesRisk ℓ, F = bayesPot ℓ = −(Bayes risk); reason: the paper's ℓ_F is a proper loss whose potential F = −E_{i∼q}ℓ(q,i) is finite (footnote 1); EReal holds the value +∞; values off the simplex are irrelevant
--   - encoding: E_{P∼μ}[ℓ(P,i)] → expLoss ℓ μ i = eexp μ ℓ(·,i) = ∫⁻ ℓ(·,i)⁺ dμ − ∫⁻ ℓ(·,i)⁻ dμ in EReal; reason: the expectation of an extended-real random variable, keeping the value +∞; the negative part is bounded for a proper loss with finite Bayes risk (ℓ(p,i) ≥ ℓ(e_i,i) ∈ ℝ on Δ_K), so it is never ⊤ − ⊤
--   - encoding: regret against outcomes i_1..i_T (fixed, p.3) → regret ℓ alg1 i for a fixed i : Fin T → Fin K, rounds 0-based, identity in EReal; reason: the paper fixes the outcome sequence (p.3); EReal keeps a possibly infinite expected loss
--   - encoding: horizon T → 1 ≤ T; reason: p̂_T = N_T/T is undefined at T = 0
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.4, display (8), p.4

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_Lam
import Definitions.Def_UCalibDirichlet_delta
import Definitions.Def_UCalibDirichlet_counts
import Definitions.Def_UCalibDirichlet_regret
import Definitions.Def_UCalibDirichlet_alg1

namespace UCalibDirichlet

/-- **Lemma 1.4 (regret decomposition).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Lemma 1.4, display (8), p.4: "For any proper loss `ℓ_F`, the regret of Algorithm 1
can be decomposed as
`Reg_F(T) = Λ_F(𝟏) − Λ_F(N_T + 𝟏) + T F(p̂_T)` [BTPL regret] `+ ∑_{t=1}^T δ^{i_t}_F(a_t)`
[stability], (8) where `δ^i_F(a) = E_{P∼Dir(a)}[ℓ_F(P, i)] − E_{P∼Dir(a+e_i)}[ℓ_F(P, i)]`."

Here `p̂_T = N_T/T` (p.3), `N_T` the label counts of the whole sequence and `a_t = N_{t−1} + 𝟏`
(p.3).

**Formalization Note.** The outcome sequence is a fixed `i : Fin T → Fin K` (p.3: "we fix the
outcome sequence"); round `t : Fin T` is 0-based, so `a_t` is `𝟏` plus the counts of the
outcomes before round `t`. `T ≥ 1` (so that `p̂_T = N_T/T` is defined). The identity is in `EReal`
(the stability terms are `EReal` differences, see `delta`). `F = bayesPot ℓ`. -/
theorem lemma_1_4 {K T : ℕ} (hT : 1 ≤ T) (ℓ : (Fin K → ℝ) → Fin K → EReal) (hℓ : IsProperLoss ℓ)
    (hfin : HasFiniteBayesRisk ℓ) (i : Fin T → Fin K) :
    regret ℓ alg1 i =
      ((Lam (bayesPot ℓ) (fun _ => 1) - Lam (bayesPot ℓ) (fun j => (counts i j : ℝ) + 1) +
          T * bayesPot ℓ (fun j => (counts i j : ℝ) / T) : ℝ) : EReal) +
        ∑ t : Fin T, delta ℓ (i t)
          (fun j => 1 + (counts (fun s : Fin t => i (Fin.castLT s (s.isLt.trans t.isLt))) j : ℝ)) := by sorry

end UCalibDirichlet
