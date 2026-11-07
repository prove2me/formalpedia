-- Prove2me | Theorems.Thm_RegevRecon_eq_42
-- name    : RegevRecon.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:49.086348+00:00
-- url     : https://prove2.me/theorems/881baf14-7f8d-4d80-b064-632bcf586532
-- title:
--   (42) — the Regev pipeline and its fidelity bound
-- statement:
--   Let $B\in\mathbb F_p^{m\times n}$, $S\subseteq\mathbb F_p$, $\beta\ge0$, and let $U_{\mathrm{dec}}$ be any unitary on received, estimate and work registers, with block error $\varepsilon_B$ on a uniform codeword. Then the agreement test accepts with probability $1-\varepsilon_B$ for every $\tau$, and when $\varepsilon_B<1$,
--
--   $$
--   E_\tau\Bigl[1-\bigl|(\langle\psi_\beta|\otimes\langle0|_{\mathrm{work}})|\Psi_{B,\tau}\rangle\bigr|^2\Bigr]\le\varepsilon_B,
--   $$
--
--   with $\tau$ uniform on $\mathbb F_p^m$. The bound is on average over $\tau$ only: for a fixed $\tau$ it can fail. It converts decoding error into state-preparation error.
--
--   Differences from the source:
--   - generalization: B from the ensemble, the decoder of Proposition 2, and a common target set S in the ensemble → every matrix B, every S ⊆ F_p and every unitary decoder with a fixed work start state; reason: the argument of (42) uses nothing else; it specializes to the source's case
--   - reading: the map (18), extended by "a reversible linear-algebra circuit" → every unitary W with the printed action on |c⟩|0⟩ for c ∈ C; reason: the source does not fix the extension, and the overlap does not depend on it because |ψ_β⟩ is constant on the cosets of ker B
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), pp.16–17; (42), p.17

import Mathlib
import Definitions.Def_RegevRecon_RegevPipeline

namespace RegevRecon

/-- **The Regev pipeline and the fidelity bound (42)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), pp.16–17: for any matrix `B`, target set `S`, `β ≥ 0` and
any coherent decoder `U_dec` with block error `ε_B`, the test accepts with probability `1 − ε_B` for every `τ`, and, when
`ε_B < 1`, `E_τ[1 − |(⟨ψ_β| ⊗ ⟨0|_work)|Ψ_{B,τ}⟩|²] ≤ ε_B`, with `τ` uniform on `F_p^m`.

**Formalization Note** Exact: no circuit, no machine. The bound holds on average over `τ` only. The statement holds for every
unitary extension `W` of the map (18), since `|ψ_β⟩` is constant on the cosets of `ker B`. -/
theorem eq_42 {p m n : ℕ} [Fact p.Prime] (B : Matrix (Fin m) (Fin n) (ZMod p)) (S : Finset (ZMod p))
    (β : ℝ) (hβ : 0 ≤ β) {W' : Type*} [Fintype W'] [DecidableEq W']
    (U : Matrix ((Fin m → ZMod p) × (Fin m → ZMod p) × W')
      ((Fin m → ZMod p) × (Fin m → ZMod p) × W') ℂ)
    (hU : U ∈ Matrix.unitaryGroup _ ℂ) (w₀ : W')
    (W : Matrix ((Fin m → ZMod p) × (Fin n → ZMod p)) ((Fin m → ZMod p) × (Fin n → ZMod p)) ℂ)
    (hW : IsKernelMap B W) :
    (∀ τ : Fin m → ZMod p, ‖acceptedState B S β U w₀ τ‖ ^ 2 = 1 - blockError B S β U w₀) ∧
    (blockError B S β U w₀ < 1 →
      ((p : ℝ) ^ m)⁻¹ * ∑ τ : Fin m → ZMod p, (1 - ‖regevOverlap B S β U w₀ W τ‖ ^ 2) ≤
        blockError B S β U w₀) := by sorry

end RegevRecon
