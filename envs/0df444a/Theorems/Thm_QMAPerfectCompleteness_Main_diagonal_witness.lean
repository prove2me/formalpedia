-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_diagonal_witness
-- name    : QMAPerfectCompleteness.Main.diagonal_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:43.277147+00:00
-- url     : https://prove2.me/theorems/4fc1cce9-32b6-489c-bf0e-769808160a0b
-- title:
--   Lemma 3.3 — succinct exact description of the diagonal entries $\Gamma_z$
-- statement:
--   Let $V$ be a verifier over $\mathcal G_2$ with $g\ge1$ gates $H\otimes H$, let $h=2g$, $A=2E$, and let $\ell$ be the clock length. For every $z\in\{0,1\}^m$ the number $\Gamma_z=\langle z|A^\ell|z\rangle$ satisfies
--
--   $$
--   0\le\Gamma_z\le 2^\ell,\qquad 2^{h\ell}\Gamma_z\in\mathbb Z.
--   $$
--
--   Moreover $\Gamma_z=p/q$ for natural numbers $p,q$, $q>0$, each with at most $(h+1)\ell$ bits. On a YES instance, that is, if some proof is accepted with probability at least $2/3$, some $z$ has $\Gamma_z>2$.
--
--   Unlike the maximum eigenvalue of $E$, the number $\Gamma_z$ is therefore an exact quantity with a polynomial-size description, which the prover can send.
--
--   **Formalization Note** The hypothesis $g\ge1$ is the source's standing assumption for §3.2 (p. 7). It is needed: for $g=0$ and $E_{zz}=1$ one has $\Gamma_z=2^\ell$, which has $\ell+1>(h+1)\ell$ bits. The $(h+1)\ell=O(h\ell)$ of the source is stated through its explicit bound.
--
--   Differences from the source:
--   - generalization: the fixed verifier $V$ of Lemma 3.1 on one input → any verifier $V$ over $\mathcal G_2$ with $g\ge1$, a YES instance being a verifier that accepts some proof with probability at least $2/3$; reason: the statement specializes to the source's verifier on any YES input; nothing else about $V$ is used
--   - encoding: the number $\Gamma_z=\langle z|A^\ell|z\rangle$ → the real part of that matrix entry; reason: $A^\ell$ is Hermitian, so the entry is real
--   - encoding: a rational description with numerator and denominator of at most $(h+1)\ell$ bits → nonnegative natural numbers $p,q$, with $q>0$, $\Gamma_z=p/q$, and Nat.size bounds on both numbers; reason: Nat.size is binary length, and allowing an unreduced description preserves existence at the stated bound
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 7, Lemma 3.3, with the standing notation of §3.1–3.2

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

open Matrix

namespace QMAPerfectCompleteness.Main

/-- Lemma 3.3 (p. 7), for a verifier over `𝒢₂` with `g ≥ 1` gates `H ⊗ H`, `h = 2g`: for every `z`,
`0 ≤ Γ_z ≤ 2^ℓ` and `2^{hℓ} Γ_z ∈ ℤ`, and `Γ_z` is a rational whose numerator and denominator have
at most `(h + 1)ℓ` bits. On a YES instance (`λ_max(E) ≥ 2/3`) some `z` has `Γ_z > 2`. -/
theorem diagonal_witness (V : Verifier gatesG2) (hg : 1 ≤ hhCount V) :
    (∀ z : V.Proof,
      0 ≤ V.gamma z ∧ V.gamma z ≤ 2 ^ ell V.proofQubits ∧
      (∃ n : ℤ, (2 : ℝ) ^ (2 * hhCount V * ell V.proofQubits) * V.gamma z = n) ∧
      ∃ p q : ℕ, 0 < q ∧ V.gamma z = (p : ℝ) / q ∧
        p.size ≤ (2 * hhCount V + 1) * ell V.proofQubits ∧
        q.size ≤ (2 * hhCount V + 1) * ell V.proofQubits) ∧
    (V.AcceptsSomeProof (2 / 3) → ∃ z : V.Proof, 2 < V.gamma z) := by sorry

end QMAPerfectCompleteness.Main
