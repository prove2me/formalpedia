-- Prove2me | Theorems.Thm_TriFormQ_corollary_5
-- name    : TriFormQ.corollary_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:44:22.350895+00:00
-- url     : https://prove2.me/theorems/dfd626d0-a6cc-4379-b6f6-50d4d391af54
-- title:
--   Corollary 5: one query computes any two-vector contraction of a 3-tensor
-- statement:
--   Let $T\in\mathbb F_q^{n\times m\times p}$ define the trilinear form $f(x,y,z)=\sum_{i,j,k}T_{ijk}x_iy_jz_k$, accessed through its evaluation oracle $|x,y,z,b\rangle\mapsto|x,y,z,b+f(x,y,z)\rangle$. For any fixed vectors in two of the three input spaces, one quantum query computes the contraction of $T$ with them exactly:
--
--   1. for fixed $x_0\in\mathbb F_q^n$, $y_0\in\mathbb F_q^m$, the vector $\big(\sum_{i,j}T_{ijk}(x_0)_i(y_0)_j\big)_{k}$, i.e. $T(x_0,y_0,\cdot)$;
--   2. for fixed $x_0$, $z_0\in\mathbb F_q^p$, the vector $T(x_0,\cdot,z_0)$;
--   3. for fixed $y_0$, $z_0$, the vector $T(\cdot,y_0,z_0)$.
--
--   In each case the algorithm depends on the fixed vectors but not on $T$, and is correct with probability $1$. These one-query contractions are the probes of the prefilter (Lemma 12) and the slice queries of the later stages.
--
--   Differences from the source:
--   - reading: for any fixed vectors in two of the three input spaces, "say $x_0$ and $y_0$" → all three choices of the two fixed arguments, as three clauses; reason: the printed pair is an example of the general claim
--   - encoding: one quantum query suffices to compute the contraction → a one-query `QueryAlg` with a classical output map, chosen before $T$, outputs the contraction with probability $1$; reason: platform query model
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Corollary 5 (One-query tensor–vector multiplication), p.12 (PDF p.15)

import Definitions.Def_QAlgorithms_Defs_Query

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Corollary 5 (One-query
tensor–vector multiplication), p.12 (PDF p.15): "Let T ∈ 𝔽_q^{n×m×p} define the trilinear form
f(x, y, z) = Σ_{i,j,k} T_{ijk} x_i y_j z_k. For any fixed vectors in two of the three input
spaces, say x₀ ∈ 𝔽_q^n and y₀ ∈ 𝔽_q^m, one quantum query to the evaluation oracle for f suffices
to compute the contraction of T with those vectors (here T(x₀, y₀, z))."

**Formalization Note.** All three choices of the two fixed arguments are stated ("say x₀, y₀" is
an instance). For each, a one-query `QAlgorithms.QueryAlg` against the standard oracle
`|x, y, z, b⟩ ↦ |x, y, z, b + f(x, y, z)⟩` and a post-processing `out`, chosen after the fixed
vectors and before the tensor, output the contraction (the coefficient vector of the remaining
linear function) with probability exactly 1. -/
theorem corollary_5 {F : Type} [Field F] [Fintype F] [DecidableEq F] (n m p : ℕ) :
    (∀ (x₀ : Fin n → F) (y₀ : Fin m → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin p → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun k => ∑ i, ∑ j, θ i j k * x₀ i * y₀ j) = 1) ∧
    (∀ (x₀ : Fin n → F) (z₀ : Fin p → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin m → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun j => ∑ i, ∑ k, θ i j k * x₀ i * z₀ k) = 1) ∧
    (∀ (y₀ : Fin m → F) (z₀ : Fin p → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin n → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun i => ∑ j, ∑ k, θ i j k * y₀ j * z₀ k) = 1) := by sorry

end TriFormQ
