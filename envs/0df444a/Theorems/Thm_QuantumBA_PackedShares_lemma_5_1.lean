-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_5_1
-- name    : QuantumBA.PackedShares.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:43.497505+00:00
-- url     : https://prove2.me/theorems/e71ecac8-c75b-4f79-9d19-8476c4840ca1
-- title:
--   Lemma 5.1 — the share encoder: privacy if D ≥ p+2σ, decoding if D ≥ p+3σ
-- statement:
--   Let $F$ be a finite field with $q$ elements, $p\ge1$, $\sigma\ge0$, and let $\alpha_1,\dots,\alpha_D$ be distinct nonzero points of $F$; $V=V_{D,\sigma,p}$ is the share encoder of eq. (4).
--
--   1. **Privacy.** If $D\ge p+2\sigma$, then for every set $A\subseteq[D]$ with $|A|\le\sigma$ and every operator $X$ on the $p$ inputs,
--   $$\operatorname{Tr}_{\bar A}\bigl(VXV^\dagger\bigr)=\operatorname{Tr}(X)\,q^{-|A|}\,I_A .$$
--   2. **Decoding.** If $D\ge p+3\sigma$, then for every basis input $s$, every basis output $y_0$ that occurs in $V|s\rangle$ and every report vector $y$ that differs from $y_0$ in at most $\sigma$ positions, $\mathrm{Dec}_{p+\sigma-1}(y)$ returns $s$ in its first $p$ coefficients.
--
--   Privacy says that any $\sigma$ outputs of a block carry no information about its inputs, even with reference systems attached; decoding permits classical reconstruction after several transfers. Both are used at every block of the sharing scheme.
--
--   Differences from the source:
--   - generalization: F_q with q = 2^d > n and D ≤ n → any finite field F and any D; reason: the identity and the decoding claim use only distinct nonzero points; the specialization to q = 2^d, D ≤ n is the source’s statement
--   - reading: if D ≥ p+3σ, readout followed by polynomial decoding recovers the inputs despite σ erroneous or missing reports → for every basis input s, every basis output y₀ in the support of V|s⟩, and every report vector y within Hamming distance σ of y₀ (a missing report replaced by any value), Dec_{p+σ−1}(y) returns s in its first p coefficients; reason: readout of V|s⟩ yields exactly the codewords of the polynomials f_{s,r}; a missing report is an erroneous one
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 24, Lemma 5.1 (PDF p. 25), with eq. (4) on p. 23

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Encoder

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 5.1 (share encoder). -/
theorem lemma_5_1 {F : Type} [Field F] [Fintype F] [DecidableEq F] (D σ p : ℕ) (hp : 1 ≤ p)
    (α : Fin D → F) (hα : Function.Injective α) (hα0 : ∀ i, α i ≠ 0) :
    (p + 2 * σ ≤ D → ∀ (Aset : Finset (Fin D)), Aset.card ≤ σ →
      ∀ Xop : Matrix (Fin p → F) (Fin p → F) ℂ,
        ptraceCompl Aset (encoder D σ p α * Xop * (encoder D σ p α)ᴴ) =
          (Matrix.trace Xop * ((Fintype.card F : ℂ) ^ Aset.card)⁻¹) • (1 : Matrix (Aset → F) (Aset → F) ℂ)) ∧
    (p + 3 * σ ≤ D → ∀ (s : Fin p → F) (y₀ y : Fin D → F), encoder D σ p α y₀ s ≠ 0 →
      hammingDist y y₀ ≤ σ →
      ∀ j : Fin p, rsDecode (p + σ - 1) α y ⟨j.1, by omega⟩ = s j) := by sorry

end QuantumBA.PackedShares
