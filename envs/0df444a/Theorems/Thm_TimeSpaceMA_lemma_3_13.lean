-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_13
-- name    : TimeSpaceMA.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:09.849057+00:00
-- url     : https://prove2.me/theorems/eff55d7d-dd14-4e3d-9f00-2da19582b9c1
-- title:
--   Lemma 3.13 — tensor facts
-- statement:
--   Let $G$ be a systematic subset-sum code with the distance of Lemma 3.10(b), $r\ge1$, and $A$ an abelian group.
--
--   1. Every line of a tensor codeword over $A$ is a codeword of $G$ over $A$.
--   2. A word over $A$ all of whose lines are codewords of $G$ is a tensor codeword.
--   3. If $Y=G^{\otimes r}z$ and $j\in[q]$, then $\beta\mapsto Y(\sigma(j),\beta)$ on $[L]^{r-1}$ equals $G^{\otimes(r-1)}$ applied to the slice $\beta'\mapsto z(j,\beta')$, along any axis.
--   4. If $z\in A^{[q]^r}$ is nonzero then $G^{\otimes r}z$ has at least $\delta^rL^r$ nonzero entries.
--   5. If $W\in\mathbb Z^{[L]^r}$ and $Y=G^{\otimes r}z$ with $z\in\mathbb Q^{[q]^r}$ satisfy $\mathrm{dist}(W,Y)<\delta^r$, then $z\in\mathbb Z^{[q]^r}$. The same holds entrywise for $\mathbb Z^d$-valued words.
--
--   Differences from the source:
--   - generalization: G the code of Lemma 3.10 → any systematic subset-sum code with the distance of Lemma 3.10(b); reason: the statement uses only these properties, and the code of Lemma 3.10 has them
--   - encoding: (c) on r axes, word on [L]^{r−1}, r ≥ 1 → r+1 axes, word on [L]^r, r ≥ 0, the fixed axis placed by Fin.insertNth; reason: the same range of r with no subtraction
--   - encoding: abelian group A → abelian group in Lean's Type; reason: Type contains the groups the paper uses
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.13, p.12

import Definitions.Def_TimeSpaceMA_tensorEncode

namespace TimeSpaceMA

variable {q L : ℕ}

open Classical in

/-- **Lemma 3.13** (Tensor facts; Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, p.12).
Parts (a)–(d) over every abelian group `A`, and part (e) over `ℚ`, with its entrywise form over `ℤ^d`.

**Formalization Note** `G` is any systematic subset-sum code with the distance of Lemma 3.10(b). Clause
(c) is on `r + 1` axes, the slice on `r`, along any axis `i`; `Fin.insertNth i (σ j) β` is `(σ(j), β)` with
`σ(j)` at position `i`. In (d), `δ^r L^r` is written with `δ = q / L`. -/
theorem lemma_3_13 (G : SubsetSumCode q L) (σ : Fin q → Fin L) (hσ : G.IsSystematic σ)
    (hG : G.HasGroupDistance) :
    (∀ (A : Type) [AddCommGroup A] (r : ℕ), 1 ≤ r → ∀ (z : (Fin r → Fin q) → A)
        (α : Fin r → Fin L) (i : Fin r), G.IsCodeword (line (tensorEncode G z) α i)) ∧
    (∀ (A : Type) [AddCommGroup A] (r : ℕ), 1 ≤ r → ∀ Y : (Fin r → Fin L) → A,
        (∀ (α : Fin r → Fin L) (i : Fin r), G.IsCodeword (line Y α i)) → IsTensorCodeword G Y) ∧
    (∀ (A : Type) [AddCommGroup A] (r : ℕ) (z : (Fin (r + 1) → Fin q) → A) (i : Fin (r + 1))
        (j : Fin q) (β : Fin r → Fin L),
        tensorEncode G z (Fin.insertNth (α := fun _ => Fin L) i (σ j) β) =
          tensorEncode G (fun β' : Fin r → Fin q => z (Fin.insertNth (α := fun _ => Fin q) i j β')) β) ∧
    (∀ (A : Type) [AddCommGroup A] (r : ℕ), 1 ≤ r → ∀ z : (Fin r → Fin q) → A, z ≠ 0 →
        G.delta ^ r * (L : ℝ) ^ r ≤
          ((Finset.univ.filter fun α => tensorEncode G z α ≠ 0).card : ℝ)) ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ (W : (Fin r → Fin L) → ℤ) (z : (Fin r → Fin q) → ℚ),
        relHamming (fun α => (W α : ℚ)) (tensorEncode G z) < G.delta ^ r →
        ∀ p, ∃ n : ℤ, z p = n) ∧
    (∀ (r d : ℕ), 1 ≤ r → ∀ (W : (Fin r → Fin L) → Fin d → ℤ) (z : (Fin r → Fin q) → Fin d → ℚ),
        relHamming (fun α k => (W α k : ℚ)) (tensorEncode G z) < G.delta ^ r →
        ∀ p k, ∃ n : ℤ, z p k = n) := by sorry

end TimeSpaceMA
