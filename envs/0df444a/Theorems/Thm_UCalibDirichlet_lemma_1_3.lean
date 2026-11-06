-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_1_3
-- name    : UCalibDirichlet.lemma_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:27.347273+00:00
-- url     : https://prove2.me/theorems/75328a6b-975a-42a8-859e-ce72e5bb0fc8
-- title:
--   Lemma 1.3 — count deletion: $\mathbb E_{\mathrm{Dir}(a+e_i)}[\ell_F(P,i)]=\Lambda_F(a)-\Lambda_F(a+e_i)$
-- statement:
--   Let $\ell_F$ be a proper loss with finite convex potential $F$. For every $a\in\mathbb R^K_{>0}$ and $i\in[K]$,
--   $$\mathbb E_{P\sim\mathrm{Dir}(a+e_i)}\big[\ell_F(P,i)\big]=\Lambda_F(a)-\Lambda_F(a+e_i),$$
--   where $\Lambda_F(a)=\|a\|_1\,\mathbb E_{P\sim\mathrm{Dir}(a)}[F(P)]$ is the Dirichlet potential.
--
--   The identity (Lemma 2 of Dewasurendra, 2026) says that the be-the-perturbed-leader forecast, which has already counted the outcome $i$, pays exactly the one-step decrease of the Dirichlet potential; telescoping gives the regret decomposition (8).
--
--   Differences from the source:
--   - encoding: proper loss ℓ_F : Δ_K × [K] → ℝ ∪ {+∞} with finite convex potential F → ℓ : (Fin K → ℝ) → Fin K → EReal with IsProperLoss ℓ and HasFiniteBayesRisk ℓ, F = bayesPot ℓ = −(Bayes risk); reason: the paper's ℓ_F is a proper loss whose potential F = −E_{i∼q}ℓ(q,i) is finite (footnote 1); EReal holds the value +∞; values off the simplex are irrelevant
--   - encoding: E_{P∼μ}[ℓ(P,i)] → expLoss ℓ μ i = eexp μ ℓ(·,i) = ∫⁻ ℓ(·,i)⁺ dμ − ∫⁻ ℓ(·,i)⁻ dμ in EReal; reason: the expectation of an extended-real random variable, keeping the value +∞; the negative part is bounded for a proper loss with finite Bayes risk (ℓ(p,i) ≥ ℓ(e_i,i) ∈ ℝ on Δ_K), so it is never ⊤ − ⊤
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.3, displays (6)–(7), p.4

import Mathlib
import Definitions.Def_UCalibDirichlet_dir
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_expLoss
import Definitions.Def_UCalibDirichlet_Lam

namespace UCalibDirichlet

/-- **Lemma 1.3 (count deletion; Lemma 2 of Dewasurendra [2026]).** Frongillo, Luo, Mehta &
Schneider (manuscript, STOC 2027 submission), Lemma 1.3, displays (6)–(7), p.4: "For any proper
loss `ℓ_F`, `a ∈ ℝ^K_{>0}`, and `i ∈ [K]`, we have
`E_{P∼Dir(a+e_i)}[ℓ_F(P, i)] = Λ_F(a) − Λ_F(a + e_i)`, (6) where `Λ_F` is the Dirichlet potential
defined as `Λ_F(a) = ‖a‖₁ E_{P∼Dir(a)}[F(P)]`. (7)"

**Formalization Note.** A proper loss `ℓ_F` is an `EReal`-valued `ℓ` with `IsProperLoss ℓ` and
finite Bayes risk (footnote 1, p.3); `F = bayesPot ℓ` is minus its Bayes risk. The left side is
`expLoss` (exact, possibly `+∞` a priori); the lemma asserts it equals the real number on the
right. -/
theorem lemma_1_3 {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (hℓ : IsProperLoss ℓ)
    (hfin : HasFiniteBayesRisk ℓ) (a : Fin K → ℝ) (ha : ∀ j, 0 < a j) (i : Fin K) :
    expLoss ℓ (dir (a + Pi.single i 1)) i =
      ((Lam (bayesPot ℓ) a - Lam (bayesPot ℓ) (a + Pi.single i 1) : ℝ) : EReal) := by sorry

end UCalibDirichlet
