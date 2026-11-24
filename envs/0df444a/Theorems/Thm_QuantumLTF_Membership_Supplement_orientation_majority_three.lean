-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_orientation_majority_three
-- name    : QuantumLTF.Membership.Supplement.orientation_majority_three
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:22:15.189465+00:00
-- url     : https://prove2.me/theorems/097d63a2-aa7f-46d9-aceb-733ccfe1a96c
-- title:
--   Three independent orientation votes have error at most 5/32
-- statement:
--   Consider three independent finite probability spaces with normalized nonnegative weights. Let their respective error events $E_1,E_2,E_3$ each have probability at most $1/4$. Then
--
--   $$\Pr\bigl((E_1\cap E_2)\cup(E_1\cap E_3)\cup(E_2\cap E_3)\bigr)\le\frac{5}{32}.$$
--
--   The three distributions and error rates may differ. This is the majority-vote probability estimate in Theorem 5.6. The single-example disagreement bound and the tomography algorithm are separate constructions.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.4, proof of Theorem 5.6, three independent orientation votes.

import Mathlib

theorem QuantumLTF.Membership.Supplement.orientation_majority_three {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α → ℝ) (q : β → ℝ) (r : γ → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) (hr : ∀ c, 0 ≤ r c)
    (hpt : ∑ a, p a = 1) (hqt : ∑ b, q b = 1) (hrt : ∑ c, r c = 1)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : ∑ a ∈ Finset.univ.filter P, p a ≤ 1/4)
    (hQ : ∑ b ∈ Finset.univ.filter Q, q b ≤ 1/4)
    (hR : ∑ c ∈ Finset.univ.filter R, r c ≤ 1/4) :
    (∑ a : α, ∑ b : β, ∑ c : γ,
      if (P a ∧ Q b) ∨ (P a ∧ R c) ∨ (Q b ∧ R c) then p a*q b*r c else 0) ≤ 5/32 := by sorry
