-- Prove2me | Theorems.Thm_QPACLarge_lemma_3_1
-- name    : QPACLarge.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:39.429231+00:00
-- url     : https://prove2.me/theorems/43b2c723-6e71-433d-92d3-cdeb217e9f4f
-- title:
--   Lemma 3.1 — the quadratic family is 4-wise independent, has a sign flip, an efficient feature map, and $O(n^2)$-size circuits
-- statement:
--   For every $n \ge 1$, the quadratic family $\{H_a = (-1)^{q_a}\}_{a \in \{0,1\}^r}$, $r = 1 + n + \binom n2$, has the following properties.
--
--   1. It is 4-wise independent under a uniform seed $a$.
--   2. It admits a global sign flip $\iota : A \to A$.
--   3. The map $J : \{\bot\} \cup \{0,1\}^n \to \{0,1\}^r$, $J(\bot) = 0^r$, $J(x) = (1, \{x_i\}, \{x_ix_j\}_{i<j})$, is injective and satisfies $H_a(x) = (-1)^{a \cdot J(x)}$; both $J$ and its inverse on its image are computable in polynomial time.
--   4. There is a constant $c$ such that for every seed $a$, $h_a = q_a$ is computed by a Boolean circuit of size at most $c\,n^2$.
--
--   This family supplies the hypotheses of both the classical zero-query learner and the quantum sampler; item 3 is what lets the isometry $W$ be implemented with polynomially many gates.
--
--   **Formalization Note** Efficiency is polynomial-time computability on the bit encodings of labels ($0\,0^n$, $1\,x$) and seeds ($a_\emptyset, a_i, a_{ij}$ lexicographically), one machine for all $n$.
--
--   Differences from the source:
--   - reading: J and its inverse on its image are efficiently computable → one polynomial-time machine maps the label code to the seed code of $J(\ell)$, and one maps the seed code of $J(\ell)$ back to the label code, for all $n$; reason: polynomial time is the paper's notion of efficiency; the codes are those of p.19 and p.23
--   - encoding: $H_a(x) = (-1)^{a\cdot J(x)}$ → $q_a(x) = a \cdot J(x)$ in $\mathbb F_2$; reason: $b \mapsto (-1)^b$ is a bijection
--   - encoding: size $O(n^2)$ → one constant $c$ with size $\le c\,n^2$ for all $n \ge 1$; reason: the meaning of $O(n^2)$ for $n \ge 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.1, pp.19–20

import Mathlib
import Definitions.Def_QPACLarge_IsKWiseIndep
import Definitions.Def_QPACLarge_HasGlobalSignFlip
import Definitions.Def_QPACLarge_qa
import Definitions.Def_QPACLarge_Jmap
import Definitions.Def_QPACLarge_seedDot
import Definitions.Def_QPACLarge_seedBits
import Definitions.Def_QPACLarge_labelBits
import Definitions.Def_QPACLarge_InSIZE

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **Lemma 3.1 (Properties of the Quadratic Boolean Family).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.1, pp.19–20: "For every `n ≥ 1`, the family `Hₙ = {H_a : {0,1}ⁿ → {−1,1}}_{a∈{0,1}^r}`
has the following properties. 1. The family is 4-wise independent under a uniform choice of the
seed `a`. 2. The family admits a global sign flip `ι : A → A`. 3. There is an injective map
`J : {⊥} ∪ {0,1}ⁿ → {0,1}^r` such that `J(⊥) = 0^r` and `H_a(x) = (−1)^{a·J(x)}`. Both `J` and its
inverse on its image are efficiently computable. 4. For every seed `a`, the Boolean function `h_a`
is computable by a deterministic classical Boolean circuit of size `O(n²)`."

**Formalization Note.** `J` is the feature map of the proof (`Jmap`). "Efficiently computable" is
polynomial-time computability (published `PolyTimeComputable`) on the bit encodings: a label as
`0·0ⁿ` / `1·x` (`labelBits`) and a seed as `a_∅, aᵢ, aᵢⱼ` in lexicographic order (`seedBits`); one
machine for all `n`. `O(n²)` is one constant `c` with size `≤ c·n²` for all `n ≥ 1`. -/
theorem lemma_3_1 :
    (∀ n : ℕ, 1 ≤ n →
      IsKWiseIndep (fun (a : Seed n) (x : Qubits n) => qa a x) 4 ∧
      HasGlobalSignFlip (fun (a : Seed n) (x : Qubits n) => qa a x) ∧
      Function.Injective (Jmap n) ∧
      Jmap n none = (false, fun _ => false, fun _ => false) ∧
      ∀ (a : Seed n) (x : Qubits n), qa a x = seedDot a (Jmap n (some x))) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ (n : ℕ) (ℓ : Option (Qubits n)), g (labelBits ℓ) = seedBits (Jmap n ℓ)) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ (n : ℕ) (ℓ : Option (Qubits n)), g (seedBits (Jmap n ℓ)) = labelBits ℓ) ∧
    (∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ a : Seed n, InSIZE (qa a) (c * n ^ 2)) := by sorry

end QPACLarge
