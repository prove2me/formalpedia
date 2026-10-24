-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_4
-- name    : RendezvousKn.Sym.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:20.92923+00:00
-- url     : https://prove2.me/theorems/0bd51282-1d48-4d2d-a5e3-3116435bd547
-- title:
--   Lemma 4, p. 4, with δ = 2⁻³⁵ from p. 11 — same-kind tactics have W(τ_A, τ_B) ≥ (n+1)/2 + 2⁻³⁵n
-- statement:
--   Fix $n\ge2$. For all tactics $\tau_A,\tau_B$ of the same kind (both passive or both active),
--   $$W(\tau_A,\tau_B)\ \ge\ \frac{n+1}{2}+2^{-35}\,n.$$
--
--   The paper states Lemma 4 as "there exists $\delta>0$" and concludes its proof (p. 11) with "Lemma 4 holds for $\delta=2^{-35}$". This is the core estimate: two tactics of the same kind wait linearly longer than the Anderson–Weber bound.
--
--   **Formalization Note** The hypothesis $n\ge2$ (§3's standing assumption) is necessary: at $n=1$, $W=1<1+\delta$.
--
--   Differences from the source:
--   - generalization: there exists δ > 0 (after n is fixed, §3) → δ = 2⁻³⁵ for every n ≥ 2; reason: the paper's proof establishes δ = 2⁻³⁵ (p. 11); the explicit uniform constant implies the existential for each n
--   - encoding: τ_A, τ_B ∈ Θ^A or τ_A, τ_B ∈ Θ^P → IsPassive τ_A ↔ IsPassive τ_B; reason: every tactic is either passive or active, so 'both in one class' is 'same passivity'
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 4 (PDF 5), Lemma 4; δ = 2⁻³⁵ on p. 11 (PDF 12), §3.6

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_4 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n)
    (hkind : IsPassive τA ↔ IsPassive τB) :
    ((n : ℝ) + 1) / 2 + (2 : ℝ) ^ (-35 : ℤ) * n ≤ W τA τB := by sorry

end RendezvousKn.Sym
