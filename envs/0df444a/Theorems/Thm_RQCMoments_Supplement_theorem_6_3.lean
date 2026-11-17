-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_6_3
-- name    : RQCMoments.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:52:10.992406+00:00
-- url     : https://prove2.me/theorems/cbf9a2df-9af7-46d4-adb2-28efb8e657d7
-- title:
--   Theorem 6.3 — appending a Haar random $m$-qubit unitary makes a design $m$-locally invariant
-- statement:
--   Let $U\sim\mu(k,\varepsilon)$ be an $\varepsilon$-approximate unitary $k$-design on $n$ qubits, and let $V$ be a Haar random unitary acting on a fixed set $S$ of $m$ qubits, independent of $U$. Then the distribution of $(V\otimes I)U$ is
--
--   1. $m$-locally invariant (Definition 6.1), and
--   2. an $\varepsilon$-approximate unitary $k$-design.
--
--   This converts a generic design into a locally invariant one at the cost of one Haar random unitary on $m$ qubits, so the total-variation results of Section 6 apply to it.
--
--   **Formalization Note** The law of $(V\otimes I)U$ is the pushforward of $\mathrm{Haar}(2^m)\otimes\mu$ under $(V,U)\mapsto(V\otimes I)U$. Local invariance is stated for the same set $S$ and, as in Definition 6.1, with existential $S$; the design property has the same $k$ and $\varepsilon$. $\varepsilon$ is any real number, as printed.
--
--   Differences from the source:
--
--   - encoding: (V ⊗ I)U with V ∼ Haar(2^m) independent of U ∼ μ(k, ε) → pushforward of Haar(2^|S|) ⊗ μ under (V, U) ↦ (V ⊗ I)U, with |S| = m; reason: law of a function of independent variables; same object
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
--   - generalization: (V ⊗ I)U is m-locally invariant (Definition 6.1: for some set of m qubits) → additionally invariant on the given set S (IsLocallyInvariantOn S); reason: the extra conjunct implies IsLocallyInvariant m since |S| = m, so the Lean specializes to the printed claim; the page's proof establishes it for S
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.3, p.39 (PDF p.41); Definition 6.1, p.38

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_IsLocallyInvariant

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 6.3** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.3, p.39, PDF p.41).
Let `U ∼ μ(k, ε)` be an `ε`-approximate unitary `k`-design on `n` qubits, and let `V` be a Haar random
unitary acting on any fixed subset `S` of `m` qubits, independent of `U`. Then `(V ⊗ I)U` is an
`m`-locally invariant `ε`-approximate unitary `k`-design.

**Formalization Note** The law of `(V ⊗ I)U` with `V ∼ Haar(2^m)` independent of `U ∼ μ` is the
pushforward of `Haar(2^m) ⊗ μ` under `(V, U) ↦ (V ⊗ I) U` (`tensorId`, `leftMulOrSelf`). Its
`m`-local invariance (Definition 6.1) is witnessed by the same set `S` (the first conjunct, which
implies `IsLocallyInvariant m` since `|S| = m`); its design property has the same `k` and `ε`
(Remark 2.3: `IsStrongDesign · k k ε`). `ε` is any real number, as printed. -/
theorem theorem_6_3 {n : ℕ} (k : ℕ) (ε : ℝ) (μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ))
    (hμ : IsStrongDesign μ k k ε) (m : ℕ) (S : Finset (Fin n)) (hS : S.card = m) :
    let law : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :=
      ((QAlgorithms.Schur.unitaryHaar (2 ^ S.card)).prod μ).map
        (fun VU => leftMulOrSelf (tensorId S (VU.1 : Matrix (Fin (2 ^ S.card)) (Fin (2 ^ S.card)) ℂ)) VU.2)
    IsLocallyInvariantOn S law ∧ IsLocallyInvariant m law ∧ IsStrongDesign law k k ε := by sorry

end Supplement

end RQCMoments
