-- Prove2me | Theorems.Thm_QMAvsQCMAH_lemma_12
-- name    : QMAvsQCMAH.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:10.623371+00:00
-- url     : https://prove2.me/theorems/9e2154c4-99ba-438b-b1b7-13c76e66c0d2
-- title:
--   Lemma 12 — a random Boolean function admits no good quantum witness
-- statement:
--   Let $\lambda,a\ge1$. Fix an oracle-free quantum algorithm $A$ that receives an $a$-qubit density operator $\sigma$ and a classical input $y\in\{0,1\}^\lambda$ and outputs an element of a finite set $K$ (in the paper, the code $C_\lambda$) or $\bot$. For a uniformly random Boolean function $B:K\times\{0,1\}^\lambda\to\{0,1\}$,
--   $$\Pr_B\Bigl[\exists\sigma:\ \Pr_{y\leftarrow\{0,1\}^\lambda,\ v\leftarrow A(\sigma,y)}[v\ne\bot\wedge B(v,y)=1]>\tfrac23\Bigr]\le6\sqrt{(a+1)2^{-\lambda}}.$$
--
--   This is the soundness core of Theorem 8: sparse noise is dominated by a uniform function, and no witness passes a single check on it with probability above $2/3$.
--
--   Differences from the source:
--   - generalization: outputs in the linear code C_λ ⊆ Σ_λ^{q_λ}; B uniform on Σ_λ^{q_λ} × {0,1}^λ → outputs in any finite set K; B uniform on K × {0,1}^λ; reason: the proof does not use linearity, and the restriction of a uniform function to C_λ × {0,1}^λ is uniform; K = C_λ gives the paper's statement
--   - encoding: an oracle-free quantum algorithm A(σ, y) → for each y a POVM A y on a qubits with outcomes Option K; reason: every oracle-free algorithm with classical input y is such a measurement, and conversely
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 12, p.40 (PDF p.43); Appendix A.2, pp.87–88

import Definitions.Def_QMAvsQCMAH_Normalized
import Definitions.Def_QMAvsQCMAH_prob

set_option autoImplicit false

namespace QMAvsQCMAH

/-- **Lemma 12 (A random Boolean function).** Let `λ, a ≥ 1`. Fix an oracle-free quantum
algorithm `A` that receives an `a`-qubit density operator `σ` and a classical input
`y ∈ {0,1}^λ` and outputs an element of a finite set `K` (the code `C_λ`) or `⊥`. For a uniform
Boolean function `B : K × {0,1}^λ → {0,1}`,
`Pr_B[∃σ : Pr_{y ← {0,1}^λ, v ← A(σ, y)}[v ≠ ⊥ ∧ B(v, y) = 1] > 2/3] ≤ 6√((a + 1)2^{−λ})`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 12, p.40 (PDF p.43): "Let λ, a ≥ 1 be integers. Fix an oracle-free quantum algorithm
A that receives an a-qubit density operator σ and a classical input y ∈ {0, 1}^λ and outputs an
element of Cλ ∪ {⊥} for the linear code Cλ ⊆ Σ_λ^{qλ} (Definition 13). For a uniform Boolean
function B : Σ_λ^{qλ} × {0, 1}^λ → {0, 1}, Pr_B[∃σ : Pr_{y←{0,1}^λ, v←A(σ,y)}[v ≠ ⊥ ∧
B(v, y) = 1] > 2/3] ≤ 6√((a + 1)2^{−λ})."

**Formalization Note.** An oracle-free quantum algorithm with input `y` is, for each `y`, a POVM
`A y` on `a` qubits with outcomes `K ∪ {⊥}` (`Option K`). The outcome set is any finite set
`K`: the proof does not use linearity, and the values of `B` off `C_λ × {0,1}^λ` are
irrelevant (the restriction of a uniform function is uniform). -/
theorem lemma_12 (lam a : ℕ) (hlam : 1 ≤ lam) (ha : 1 ≤ a) {K : Type} [Fintype K] [DecidableEq K] (A : (Fin lam → Bool) → Option K → Matrix (Fin a → Bool) (Fin a → Bool) ℂ) (hA : ∀ y, IsPOVM (A y)) : prob (fun _ : K × (Fin lam → Bool) → Bool => ((2 : ℝ) ^ Fintype.card (K × (Fin lam → Bool)))⁻¹) (fun B => ∃ σ : Matrix (Fin a → Bool) (Fin a → Bool) ℂ, IsDensity σ ∧ (2 : ℝ) / 3 < ((2 : ℝ) ^ lam)⁻¹ * ∑ y : Fin lam → Bool, ∑ v : K, (if B (v, y) then ((A y (some v) * σ).trace).re else 0)) ≤ 6 * Real.sqrt (((a : ℝ) + 1) * (2 : ℝ)⁻¹ ^ lam) := by sorry

end QMAvsQCMAH
