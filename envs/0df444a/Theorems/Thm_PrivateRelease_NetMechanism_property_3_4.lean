-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_property_3_4
-- name    : PrivateRelease.NetMechanism.property_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:46.45471+00:00
-- url     : https://prove2.me/theorems/fb4497fb-5e2c-4d82-b28b-340fe51b3006
-- title:
--   Property 3.4 — the Net mechanism is (2α, δ)-useful once α ≥ (2Δ/ε) log(|N_α(C)|/δ)
-- statement:
--   Let $X$ be a finite data universe, $n\ge1$ the input size, and $\mathcal Q$ any class of real-valued queries on databases (not necessarily counting queries). Let $\Delta$ be an upper bound on the global sensitivities, $GS_Q\le\Delta$ for every $Q\in\mathcal Q$; the paper takes $\Delta=\max_{Q\in\mathcal Q}GS_Q$. Let $N$ be a minimum $\alpha$-net for $\mathcal Q$, and assume the Net mechanism's quality score $q(z,D')=-\max_{Q\in\mathcal Q}|Q(z)-Q(D')|$ is real-valued (the family $|Q(z)-Q(D')|$, $Q\in\mathcal Q$, is bounded for each input $z$ and each $D'\in N$) and has positive sensitivity. If $\varepsilon>0$, $0<\delta\le1$ and
--   $$
--   \alpha\ \ge\ \frac{2\Delta}{\varepsilon}\,\log\frac{|N|}{\delta},
--   $$
--   then the Net mechanism run on $N$ is $(2\alpha,\delta)$-useful for $\mathcal Q$: for every input $z\in X^n$, with probability at least $1-\delta$ its output $\hat D$ satisfies $|Q(\hat D)-Q(z)|\le 2\alpha$ for all $Q\in\mathcal Q$.
--
--   This is the paper's general reduction: the accuracy of the Net mechanism is governed only by the sensitivity of the queries and the size of the smallest α-net.
--
--   **Formalization Note** The paper's "$\log N_\alpha(C)/\delta$" is the logarithm of $|N_\alpha(C)|/\delta$. Stating the result for every common upper bound $\Delta$ of the sensitivities contains the paper's case $\Delta=\max_Q GS_Q$ and avoids a junk supremum when the class is infinite. The boundedness hypothesis is the paper's typing $q:X^*\times R\to\mathbb R$; the hypothesis $GS_q>0$ is where the exponential mechanism's formula is defined. Neighbours differ in exactly one entry.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 8, Property 3.4

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

namespace PrivateRelease.NetMechanism

/-- Property 3.4 (p. 8): for any class `QC` of real queries on databases (not necessarily
counting queries) whose sensitivities are all at most `Δ`, the Net mechanism run on a minimum
α-net `N` is `(2α, δ)`-useful whenever `α ≥ (2Δ/ε) log(|N|/δ)`. The quality score is assumed
real-valued (the family `|Q(z) − Q(D′)|`, `Q ∈ QC`, is bounded) and of positive sensitivity, as
Definition 3.1 and Algorithm 1 require. -/
theorem property_3_4 {X : Type} [Fintype X] {n : ℕ} (hn : 1 ≤ n) (QC : Set (Multiset X → ℝ))
    (ε α δ Δ : ℝ) (N : Finset (Database X)) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : IsMinNet QC α N) (hsens : 0 < netSens n QC N)
    (hΔ : ∀ Q ∈ QC, GS (fun z : Fin n → X => Q (inputDB z)) ≤ Δ)
    (hbdd : ∀ (z : Fin n → X), ∀ D' ∈ N,
      BddAbove (Set.range fun Q : QC => |Q.1 (inputDB z) - Q.1 D'.1|))
    (hα : 2 * Δ / ε * Real.log ((N.card : ℝ) / δ) ≤ α) :
    Useful QC (2 * α) δ (netMech (n := n) QC ε N) := by sorry

end PrivateRelease.NetMechanism
