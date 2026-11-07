-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_8
-- name    : TimeSpaceMA.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:52.989055+00:00
-- url     : https://prove2.me/theorems/410fdcca-7299-41e6-b5f6-82316ddebf97
-- title:
--   Lemma 3.8(a)–(c) — properties of chunk constraints
-- statement:
--   Let $c,c'$ be configurations (bit strings of length $S$) and $v\in\mathbb Z^d$.
--
--   1. $E(v,c,c')\ge 0$.
--   2. $E(v,c,c')=0$ if and only if the run of $B$ steps from $c$ ends at $c'$ and $v$ is its record.
--   3. There are linear maps $f,f':\mathbb Z^{d+2S+1}\to\mathbb Z^F$ with $F=O(B(g+H))$ such that, writing $\Phi(y,y'):=\langle f(y),f'(y')\rangle$, one has $\Phi(y,y)=E(v,c,c')$ for $y=(v,1,c,c')$.
--
--   This turns correctness of a chunk of $B$ steps into a root of a bilinear form evaluated on the diagonal.
--
--   Differences from the source:
--   - generalization: the transition circuit of the machine M, with H ≥ S a power of 2 → any NAND circuit with S+1 inputs, g gates in topological order, output gates and address wires; H = 2^lg; reason: the statement concerns only those features of the circuit, and the machine's circuit is an instance
--   - encoding: F = O(B(g + H)) = Õ(BH) → an absolute C₀ with F ≤ C₀·B·(g + 2^lg), assuming B ≥ 1 and S ≤ 2^lg; the second equality (Õ(BH)) is dropped; reason: the O is uniform over circuits; S ≤ H is a standing assumption on p.7; Õ(BH) follows from g = Õ(S), which is a property of the machine's circuit
--   - encoding: clause (d), costs → not stated in this item; reason: clause (d) measures operations; those costs enter through the running times of the goal theorem
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.8(a)–(c), p.10

import Definitions.Def_TimeSpaceMA_chunkConstraint

namespace TimeSpaceMA

/-- **Lemma 3.8(a)–(c)** (Properties of chunk constraints; Williams, Xi, STOC 2027 submission, manuscript
sha256 184c2f95…, p.10). (a) `E(v, c, c′)` is nonnegative. (b) It vanishes exactly when the run of `B`
steps from `c` ends at `c′` and `v` is its record. (c) There are linear maps `f, f′` into `ℤ^F`, with
`F = O(B(g + H))`, such that `⟨f(y), f′(y)⟩ = E(v, c, c′)` for `y = (v, 1, c, c′)`.

**Formalization Note** The circuit is any NAND circuit with distinguished address wires, `H = 2^lg`, and
`C₀` is absolute. The bound in (c) uses `S ≤ H`, assumed on p.7. Clause (d) is about costs and is carried
by the goal's running times. -/
theorem lemma_3_8 :
    (∀ {S g lg B : ℕ} (C : TransitionCircuit S g lg) (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool)
        (v : ChunkIndex B g (2 ^ lg) → ℤ) (c c' : Fin S → Bool),
        0 ≤ chunkConstraint C X v c c') ∧
    (∀ {S g lg B : ℕ} (C : TransitionCircuit S g lg) (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool)
        (v : ChunkIndex B g (2 ^ lg) → ℤ) (c c' : Fin S → Bool), 1 ≤ B →
        (chunkConstraint C X v c c' = 0 ↔ C.runConfig X c B = c' ∧ v = chunkRecord C X c)) ∧
    (∃ C₀ : ℕ, ∀ {S g lg B : ℕ} (C : TransitionCircuit S g lg)
        (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool), 1 ≤ B → S ≤ 2 ^ lg →
        ∃ F : ℕ, F ≤ C₀ * (B * (g + 2 ^ lg)) ∧
          ∃ f f' : (ChunkInput S B g (2 ^ lg) → ℤ) →ₗ[ℤ] (Fin F → ℤ),
            ∀ (v : ChunkIndex B g (2 ^ lg) → ℤ) (c c' : Fin S → Bool),
              ∑ i, f (chunkY v c c') i * f' (chunkY v c c') i = chunkConstraint C X v c c') := by sorry

end TimeSpaceMA
