-- Prove2me | Theorems.Thm_RegevLWE_Correctness_residue_eq
-- name    : RegevLWE.Correctness.residue_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:42.424021+00:00
-- url     : https://prove2.me/theorems/3aeb991a-0e93-466a-af25-b9084821b23d
-- title:
--   Proof of Lemma 5.1, p. 34:36 — the decryption residue b − ⟨a, s⟩ equals Σ_{i∈S} e_i (plus ⌊p/2⌋ for bit 1)
-- statement:
--   Let $p \ge 1$, $n, m \ge 0$, $s \in \mathbb Z_p^n$, $a_1, \dots, a_m \in \mathbb Z_p^n$, $e_1, \dots, e_m \in \mathbb Z_p$, and let $(a_i, b_i)_{i=1}^m$ with $b_i = \langle a_i, s\rangle + e_i$ be the public key of Regev's cryptosystem. For any subset $S \subseteq [m]$, let $(a, b)$ be the encryption of a bit under $S$, so that $a = \sum_{i\in S} a_i$. Then
--   $$b - \langle a, s\rangle = \sum_{i\in S} e_i \quad\text{for the bit } 0, \qquad b - \langle a, s\rangle = \Bigl\lfloor \frac p2 \Bigr\rfloor + \sum_{i\in S} e_i \quad\text{for the bit } 1 .$$
--
--   The identity reduces the correctness of decryption to the size of the accumulated noise $\sum_{i\in S} e_i$.
--
--   **Formalization Note** The page states the bit-0 case and says the bit-1 case is similar; both are stated. No hypothesis on $p$ beyond `[NeZero p]` is needed for this algebraic identity.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, proof of Lemma 5.1 (display and the sentence after it)

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open Matrix

namespace RegevLWE.Correctness

/-- Proof of Lemma 5.1 (Regev, J. ACM 2009, p. 34:36): for the public key `(aᵢ, bᵢ)` with
`bᵢ = ⟨aᵢ, s⟩ + eᵢ` and any subset `S ⊆ [m]`, the encryption `(a, b)` of `0` satisfies
`b − ⟨a, s⟩ = ∑_{i∈S} eᵢ`, and the encryption `(a, b)` of `1` satisfies
`b − ⟨a, s⟩ = ⌊p/2⌋ + ∑_{i∈S} eᵢ` ("the proof for an encryption of 1 is similar"). -/
theorem residue_eq {p : ℕ} [NeZero p] {n m : ℕ} (a : Fin m → Fin n → ZMod p)
    (s : Fin n → ZMod p) (e : Fin m → ZMod p) (S : Finset (Fin m)) :
    (encrypt (publicKey a s e) 0 S).2 - (encrypt (publicKey a s e) 0 S).1 ⬝ᵥ s
        = ∑ i ∈ S, e i ∧
      (encrypt (publicKey a s e) 1 S).2 - (encrypt (publicKey a s e) 1 S).1 ⬝ᵥ s
        = ((p / 2 : ℕ) : ZMod p) + ∑ i ∈ S, e i := by sorry

end RegevLWE.Correctness
