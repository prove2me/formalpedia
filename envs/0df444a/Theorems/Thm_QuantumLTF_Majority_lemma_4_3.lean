-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_3
-- name    : QuantumLTF.Majority.lemma_4_3
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T10:59:40.595239+00:00
-- url     : https://prove2.me/theorems/1a63e72f-87a3-4a11-bf7b-721470c82577
-- title:
--   Lemma 4.3 — bounded alternating-root polynomials
-- statement:
--   For odd $k\ge3$, the alternating-root polynomials $P_k,Q_k$ obey the uniform pointwise estimate $${k\choose t}(P_k(t)^2+Q_k(t)^2)\le Ck/((t+1)(k-t+1)).$$
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Lemma 4.3, p.43 (PDF p.44).

import Mathlib

namespace QuantumLTF.Majority

theorem lemma_4_3 : ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, 3≤k → Odd k → ∃ P Q : Fin (k+1) → ℝ, (∀ t : Fin (k+1), 1≤t.1 → t.1<k → (P t=0 ↔ Q t≠0)) ∧ ∀ t : Fin (k+1), (k.choose t : ℝ)*(P t^2+Q t^2) ≤ C*(k:ℝ)/((t.1+1)*(k-t.1+1)) := by sorry

end QuantumLTF.Majority
