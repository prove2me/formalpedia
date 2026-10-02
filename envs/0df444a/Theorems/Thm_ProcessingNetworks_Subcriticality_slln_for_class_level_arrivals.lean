-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_slln_for_class_level_arrivals
-- name    : ProcessingNetworks.Subcriticality.slln_for_class_level_arrivals
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:26:16.263296+00:00
-- url     : https://prove2.me/theorems/1b9e6e64-9bcd-4674-b1c9-adc8c5f04c00
-- title:
--   Proposition 4.1 — SLLN for class-level arrivals
-- statement:
--   In the alternate-routing-with-immediate-commitment model (Section 4.2), uncommitted arrivals
--   from $L$ sources ($U_\ell$, rate $\nu_\ell > 0$) must be routed immediately into an eligible
--   buffer, recorded by the cumulative process $V_{\ell i}(t)$ (arrivals from source $\ell$ routed
--   to buffer $i$ by time $t$), subject to $V_{\ell i} \equiv 0$ whenever $G_{\ell i} = 0$ (source
--   $\ell$ may not use buffer $i$) and $\sum_i V_{\ell i}(t) = U_\ell(t)$. The induced class-level
--   arrival process is $E_i(t) := \sum_\ell V_{\ell i}(t)$.
--
--   **Proposition 4.1.** If the SPN is stable (its ambient Markov chain is positive recurrent),
--   there exist a matrix $\varphi \in \mathbb{R}_+^{L\times I}$ and a vector $\lambda \in
--   \mathbb{R}_+^I$ such that, almost surely,
--   $$
--   \lim_{t\to\infty} \frac{1}{t} V(t) = \varphi, \qquad \lim_{t\to\infty} \frac{1}{t} E(t) = \lambda,
--   $$
--   and moreover
--   $$
--   \varphi_{\ell i} = 0 \text{ if } G_{\ell i} = 0, \qquad \sum_{i} \varphi_{\ell i} = \nu_\ell
--   \ \text{ for all } \ell, \qquad \lambda_i = \sum_{\ell} \varphi_{\ell i} \ \text{ for all } i.
--   $$
--
--   This is a strong law of large numbers for the class-level arrival process induced by a
--   randomized, state-dependent routing policy, obtained (in the book's proof) via a regenerative
--   argument at the return times of the positive recurrent ambient chain. It is the tool Corollary
--   5.5 uses to reduce necessity of subcriticality for the alternate-routing model to the ordinary
--   static planning problem's necessity argument.
--
--   **Formalization note.** The proposition is stated for the augmented model exactly as Section 4.2
--   sets it up: uncommitted arrivals $U$ with the SLLN (4.5) at strictly positive long-run rates
--   $\nu$ (independent Poisson sources, or a MArP via Proposition E.7(a)); the routing process $V$
--   with (4.6) and the class-level arrivals $E$ with (4.7); the SPN embedded in an ambient chain $X$
--   (Assumption 3.1 in its modified form (4.4)) that is stable (positive recurrent, `IsStable M`);
--   the exit rates of $X$ bounded (Eq. (D.8), which every generator in the book satisfies and which
--   the regenerative argument of the proof uses to give the routing increments per cycle a finite
--   mean); and the simply structured routing rule (4.8) recorded through mission I's
--   `IsJumpFunctional`: $V$ moves only at the transitions of $X$, by an increment determined by the
--   transition. Without that last hypothesis nothing would tie $V$ to the chain, and the a.s. limits
--   (4.10) could fail.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 71, Proposition 4.1

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

/-- Proposition 4.1 (SLLN for class-level arrivals), p. 71 (PDF p. 87). `U` is the `L`-dimensional
process of uncommitted arrivals from `L` sources, obeying the SLLN (4.5) with strictly positive
long-run rates `ν` (independent Poisson sources, or a Markovian arrival process, Proposition
E.7(a)); `G` is the zero-one source-buffer matrix of available routing options; `V` is the
routing process (`V ℓ i t` = cumulative arrivals from source `ℓ` routed to buffer `i` by time
`t`, Eq. (4.6)); `E` is the induced class-level arrival process (Eq. (4.7)). The SPN is embedded
in an ambient chain `M` (Assumption 3.1 in the modified form (4.4)) whose exit rates are bounded
(Eq. (D.8), which every generator in the book satisfies), and the routing process is a functional
of the ambient chain's jumps (the simply structured routing rule (4.8): `V` moves only at the
arrival transitions of `X`, by an increment determined by the transition). Assuming the SPN is
stable (the ambient chain is positive recurrent), there exist a routing-rate matrix `φ` and a
class-arrival-rate vector `λ` realizing the a.s. limits (4.10) and satisfying the balance
identities (4.11)–(4.12). -/
theorem slln_for_class_level_arrivals
    {Ω : Type*} [MeasureSpace Ω] {L I J : ℕ} {Xstate : Type*} [Countable Xstate]
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (hrate : ∃ C : ℝ, ∀ x, M.rate x ≤ C)
    (G : Matrix (Fin L) (Fin I) ℝ) (hG : ∀ ℓ i, G ℓ i = 0 ∨ G ℓ i = 1)
    (U : Fin L → ℝ → Ω → ℕ) (nu : Fin L → ℝ) (hnu : ∀ ℓ, 0 < nu ℓ)
    (hU : ℙ {ω | Filter.Tendsto (fun t : ℝ => fun ℓ => (U ℓ t ω : ℝ) / t)
        Filter.atTop (nhds nu)} = 1)
    (V : Fin L → Fin I → ℝ → Ω → ℕ)
    (hVG : ∀ ℓ i, G ℓ i = 0 → ∀ (t : ℝ) (ω : Ω), V ℓ i t ω = 0)
    (hVsum : ∀ (ℓ : Fin L) (t : ℝ) (ω : Ω), ∑ i, V ℓ i t ω = U ℓ t ω)
    (hVjump : ∃ g : Xstate → Xstate → Fin L → Fin I → ℕ,
      IsJumpFunctional M (fun t ω => fun ℓ i => V ℓ i t ω) g)
    (E : Fin I → ℝ → Ω → ℕ) (hE : ∀ (i : Fin I) (t : ℝ) (ω : Ω), E i t ω = ∑ ℓ, V ℓ i t ω)
    (hstable : IsStable M) :
    ∃ (phi : Fin L → Fin I → ℝ) (lam : Fin I → ℝ),
      ℙ {ω | Filter.Tendsto (fun t : ℝ => fun ℓ i => (V ℓ i t ω : ℝ) / t)
          Filter.atTop (nhds phi)} = 1 ∧
      ℙ {ω | Filter.Tendsto (fun t : ℝ => fun i => (E i t ω : ℝ) / t)
          Filter.atTop (nhds lam)} = 1 ∧
      (∀ ℓ i, G ℓ i = 0 → phi ℓ i = 0) ∧
      (∀ ℓ, ∑ i, phi ℓ i = nu ℓ) ∧
      (∀ i, lam i = ∑ ℓ, phi ℓ i) := by sorry

end ProcessingNetworks.Subcriticality
