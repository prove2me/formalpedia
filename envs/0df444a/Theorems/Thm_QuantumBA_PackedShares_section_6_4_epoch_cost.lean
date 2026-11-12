-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_section_6_4_epoch_cost
-- name    : QuantumBA.PackedShares.section_6_4_epoch_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:20.544189+00:00
-- url     : https://prove2.me/theorems/f33eb53a-55e5-49f3-8416-a7d00d4c5745
-- title:
--   Section 6.4 — one epoch costs O_ε(nL⁸) qubits, O_ε(n²L⁸) bits and O_ε(L⁴) rounds, deterministically
-- statement:
--   Fix $0<\varepsilon<1/3$ and take the parameters (11) with $c=1$, $L=\lceil\log_2n\rceil$. There is a constant $C_\varepsilon$ such that for every $n\ge2$ and $t\le(1/3-\varepsilon)n$, every input vector, adversary and public choice, on every execution, every epoch of QBA:PackedShares charges at most
--   $$C_\varepsilon\,nL^8\ \text{qubits},\qquad C_\varepsilon\,n^2L^8\ \text{classical bits},$$
--   and has $1+h(4bw+3)+4(w+1)\le C_\varepsilon L^4$ rounds.
--
--   The bounds hold also in failed elections, because they rely only on the per-sender, per-slot and per-requester caps; multiplied by the expected number of epochs they give Theorem 1.
--
--   Differences from the source:
--   - reading: for h ≥ 1 … ; if h = 0 … also within the stated bounds; Oε,c with c = 1 → one constant C(ε) for every n ≥ 2, both cases h = 0 and h ≥ 1, with L = ⌈log₂ n⌉; reason: the section covers both cases; n = 1 has no epoch
--   - generalization: qubits and classical bits sent while honest → every transmission staged by a process honest at the honest step is charged, even if the sender is corrupted later in the round; reason: a larger count; the paper notes its upper bounds also hold for it (§1.1, PDF 3)
--   - generalization: a fixed field F_q with q = 2^d, a fixed nonzero F2-linear ψ, fixed distinct nonzero evaluation points, a fixed F2-basis → the statement holds for every field F with |F| = 2^d, every additive ψ : F → ZMod 2 with ψ ≠ 0, every injective nonzero α : Fin n → F (a block with D outputs uses α_1, …, α_D) and every additive equivalence F ≃ (Fin d → ZMod 2); reason: the paper fixes arbitrary such choices; the statement for all of them specializes to any fixed one
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, pp. 32–33, §6.4 (PDF pp. 33–34)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Section 6.4: deterministic cost of one epoch of QBA:PackedShares with the parameters (11). -/
theorem section_6_4_epoch_cost (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n t : ℕ), 2 ≤ n → (t : ℝ) ≤ (1 / 3 - ε) * n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = 2 ^ parDbits n →
      ∀ (cf : Choices n F), Function.Injective cf.α → (∀ i, cf.α i ≠ 0) → cf.ψ ≠ 0 →
      ∀ (x : Fin n → Bool) (A : Adv (ctx11 ε n t cf)) (ω : ℕ → Outcome F),
        IsExecution (qba (ctx11 ε n t cf)) x A t ω → ∀ e : ℕ,
          (epochQ (ctx11 ε n t cf) x A ω e : ℝ) ≤ C * n * (logL n : ℝ) ^ 8 ∧
          (epochC (ctx11 ε n t cf) x A ω e : ℝ) ≤ C * (n : ℝ) ^ 2 * (logL n : ℝ) ^ 8 ∧
          ((ctx11 ε n t cf).epochLen : ℝ) ≤ C * (logL n : ℝ) ^ 4 := by sorry

end QuantumBA.PackedShares
