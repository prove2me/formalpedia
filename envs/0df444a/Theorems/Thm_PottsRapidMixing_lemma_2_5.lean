-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_5
-- name    : PottsRapidMixing.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:44.611493+00:00
-- url     : https://prove2.me/theorems/6d0225b8-666f-469b-8137-15f931dd6eb0
-- title:
--   Lemma 2.5, p.11 — local entropy and the Dirichlet form
-- statement:
--   Let $\Delta\in\mathbb N$, $q\ge2$ and $\beta>0$. There is a constant $C>0$, depending only on $q$, $B=e^\beta$ and $\Delta$, such that for every finite graph $G$ of maximum degree at most $\Delta$ on $n$ vertices and every $f:[q]^V\to\mathbb R$ with $\mathbb E_\mu[f^2]>0$, the probability measure $\nu_f=f^2\mu/\mathbb E_\mu[f^2]$ satisfies
--   $$\mathbb E_\mu[f^2]\,I_\mu(\nu_f)\le C\,n\,\mathcal E_{\mathrm{Gl}}(f).$$
--
--   This is the escape half of the dichotomy: a law with large aggregate local entropy has a large Dirichlet form.
--
--   Differences from the source:
--   - generalization: G a random Δ-regular graph (§2 setting) → every finite graph of maximum degree at most Δ, with no bound on Δ; reason: p.45 says the lemma holds for all graphs and parameter values, and the proof uses only the degree bound; it specializes to the source
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.5, p.11; p.45

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_mm_mcmc
import Definitions.Def_PottsRapidMixing_CondLaw
import Definitions.Def_PottsRapidMixing_PottsLaw

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.5** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.11). There is a constant `C > 0`,
depending only on `q`, `B` and `Δ`, such that for every `f : [q]^V → ℝ` with `E_µ[f²] > 0`, the
probability measure `ν_f := f² µ / E_µ[f²]` satisfies `E_µ[f²] I_µ(ν_f) ≤ C n E_Gl(f)`.

**Formalization Note.** `C` comes before the graph. By p.45 the lemma holds on all graphs; it is stated
for every finite graph of maximum degree at most `Δ`, with no restriction on `Δ`. -/
theorem lemma_2_5 (Δ q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ f : (V → Fin q) → ℝ,
        0 < ∑ σ, pottsLaw G β q σ * f σ ^ 2 →
        (∑ σ, pottsLaw G β q σ * f σ ^ 2) *
            localEntropy (pottsLaw G β q)
              (fun σ => f σ ^ 2 * pottsLaw G β q σ / ∑ σ', pottsLaw G β q σ' * f σ' ^ 2)
          ≤ C * (Fintype.card V : ℝ) *
            LogSobolevMC.ChiSquare.dirichlet (MarkovMixing.glauber (pottsLaw G β q))
              (pottsLaw G β q) f f := by sorry

end PottsRapidMixing
