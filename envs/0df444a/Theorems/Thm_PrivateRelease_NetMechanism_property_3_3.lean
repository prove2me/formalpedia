-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_property_3_3
-- name    : PrivateRelease.NetMechanism.property_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:21.753096+00:00
-- url     : https://prove2.me/theorems/405e7d89-43fd-414e-a8f1-8e5b96eb486d
-- title:
--   Property 3.3 — the Net mechanism is ε-differentially private
-- statement:
--   Let $X$ be a finite data universe, $n$ an input size, $\mathcal Q$ a class of real-valued queries on databases, $\alpha$ a real number and $N$ a minimum $\alpha$-net for $\mathcal Q$ (the paper's $N_\alpha(C)$), and suppose the Net mechanism's quality score $q(z,D')=-\max_{Q\in\mathcal Q}|Q(z)-Q(D')|$ has positive sensitivity $GS_q$ over $N$. Then for every $\varepsilon>0$ the Net mechanism with parameter $\varepsilon$ is $\varepsilon$-differentially private:
--   $$
--   \Pr[\mathrm{Net}(z)\in S]\le e^{\varepsilon}\,\Pr[\mathrm{Net}(z')\in S]
--   $$
--   for all inputs $z,z'$ differing in one entry and all sets $S$ of output databases, and each output law is a probability distribution.
--
--   Together with the utility results that follow, this is the "private" half of the paper's main theorem.
--
--   **Formalization Note** Neighbours differ in exactly one entry. The hypothesis $GS_q>0$ is where the exponential mechanism's formula is defined.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 8, Property 3.3

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

namespace PrivateRelease.NetMechanism

open MeasureTheory

/-- Property 3.3 (p. 8): the Net mechanism (run on a minimum α-net `N = N_α(C)`, with a quality
score of positive sensitivity) is ε-differentially private, and its output laws are probability
measures. -/
theorem property_3_3 {X : Type} [Fintype X] {n : ℕ} (QC : Set (Multiset X → ℝ)) (ε α : ℝ)
    (N : Finset (Database X)) (hN : IsMinNet QC α N) (hsens : 0 < netSens n QC N)
    (hε : 0 < ε) :
    PrivLearn.Generic.IsDP (netMech (n := n) QC ε N) ε ∧
      ∀ z : Fin n → X, IsProbabilityMeasure (netMech QC ε N z) := by sorry

end PrivateRelease.NetMechanism
