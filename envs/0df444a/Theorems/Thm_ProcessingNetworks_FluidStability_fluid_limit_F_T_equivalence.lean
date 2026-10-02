-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_fluid_limit_F_T_equivalence
-- name    : ProcessingNetworks.FluidStability.fluid_limit_F_T_equivalence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:36:59.00299+00:00
-- url     : https://prove2.me/theorems/06fa8d1a-3475-45b6-930f-314abe0b5a9e
-- title:
--   Lemma 6.8 — equivalence of scaled completion and effort limits
-- statement:
--   **Lemma 6.8.** Fix a sample point $\omega$ at which the SLLN (2.15) for service times and the
--   negligibility condition (6.38), $\frac{1}{n}\max_{1\le \ell \le n} v_j(\ell,\omega) \to 0$,
--   both hold. For an arbitrary sequence of initial states $\{x_n\}$, an arbitrary sequence of
--   scaling parameters $\{r_n\} \subset \mathbb{R}_{\ge 0}$ with $r_n \to \infty$, and each
--   $t \ge 0$:
--   $$
--   \lim_{n\to\infty} \frac{1}{r_n} F_j^{x_n}(r_n t, \omega) \text{ exists}
--   \quad\Longleftrightarrow\quad
--   \lim_{n\to\infty} \frac{1}{r_n} T_j^{x_n}(r_n t, \omega) \text{ exists},
--   $$
--   and, denoting the two limits (when they exist) by $\hat F_j(t)$ and $\hat T_j(t)$,
--   $m_j \hat F_j(t) = \hat T_j(t)$.
--
--   This is the second of the two lemmas behind Theorem 6.5, connecting the scaled service-effort
--   limit (given by Lemma 6.7) to a scaled service-completion limit, via the SLLN for the
--   "delayed random walk" $V^x_j$ (Lemma 6.9) and the renewal-theoretic "key relationship" (6.51)
--   between $V^x_j$, $T^x_j$ and $F^x_j$.
--
--   **Formalization note.** The existence-equivalence and the value-relationship are stated as
--   two separate conjuncts rather than folded into a single existential, since Lean limits are
--   unique (so any two witnesses of the same `Tendsto` statement coincide) but a single combined
--   existential would obscure that the "furthermore" clause holds for *every* pair of limits
--   satisfying the two `Tendsto` hypotheses, not just some pair. The negligibility condition (6.38)
--   is $\frac{1}{n}\max_{\ell < n} v_j(\ell) \to 0$ in the mission's indexing (`v j ℓ` is the
--   book's $v_j(\ell+1)$). The relationship between $F^x_j$, $T^x_j$ and $V^x_j$ that the proof
--   uses is the key relationship (6.51), a field of the standard setup `SPNProcessFamily`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 116, Lemma 6.8

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Lemma 6.8, Dai & Harrison p. 116 (PDF p. 132): fix `ω` at which the SLLN (2.15) for service
times and the negligibility condition (6.38) both hold. For an arbitrary sequence of initial
states `{xₙ}` and an arbitrary sequence of scaling parameters `{rₙ} ⊂ ℝ_{≥0}` with `rₙ → ∞`, and
each `t ≥ 0`: `lim_{n→∞} (1/rₙ) F^{xₙ}_j(rₙt,ω)` exists iff `lim_{n→∞} (1/rₙ) T^{xₙ}_j(rₙt,ω)`
exists (6.41)-(6.42); furthermore, denoting by `F̂_j(t)`, `T̂_j(t)` the limits when they exist,
`m_j F̂_j(t) = T̂_j(t)` (6.43). -/
theorem fluid_limit_F_T_equivalence
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0))
    (x : ℕ → Xstate) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (t : ℝ) (ht : 0 ≤ t) (j : Fin J) :
    ((∃ Fhj : ℝ, Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj)) ↔
     (∃ Thj : ℝ, Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj))) ∧
    (∀ Fhj Thj : ℝ,
      Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj) →
      Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj) →
      dat.m j * Fhj = Thj) := by sorry

end ProcessingNetworks.FluidStability
