-- Prove2me | Theorems.Thm_ReplParity_lemma_3_3
-- name    : ReplParity.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:08.496413+00:00
-- url     : https://prove2.me/theorems/f947e61c-bf2f-4c17-af3c-f074a04e4cda
-- title:
--   Lemma 3.3 — replicable gate (for the construction of its proof)
-- statement:
--   Fix $n$, a distribution $Q$ on $\mathbb F_2^n$, a subspace $V$, and $0<q,\eta<1$; let $p=Q(\mathbb F_2^n\setminus V)$. The gate of the proof uses $N_g=\lceil512/(q\eta^2)\rceil$ samples and a shared uniform $J\in\{0,\dots,B-1\}$, and outputs "continue" or "skip". It satisfies:
--
--   1. two runs on independent samples with a shared seed disagree with probability at most $\eta$;
--   2. if $p>q$, the gate skips with probability at most $\eta$;
--   3. if $p<q/4$, the gate continues with probability at most $\eta$.
--
--   Differences from the source:
--   - reading: there is a finite-bit test → the finite-bit test of the proof (gate q η V, threshold θ with a shared uniform J); reason: the construction witnesses the existential; the statement is about it so that solvers formalize the paper's algorithm
--   - generalization: rational parameters (finite-bit model, §2.2) → real parameters; reason: every rational is real, so the statement specializes to the paper's
--   - encoding: "continue" / "skip", a shared uniform J → true / false, J uniform on Fin B; probabilities as finite sums; reason: same outcomes and probabilities
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Lemma 3.3, p.17 (PDF p.19) and its proof

import Mathlib
import Definitions.Def_ReplParity_gate
import Definitions.Def_ReplParity_prIID
import Definitions.Def_ReplParity_massOutside

namespace ReplParity

/-- **Lemma 3.3 (Replicable gate), for the construction of its proof.** Shen, Zhong, *Replicable
Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission
(manuscript sha256 40424491…), Lemma 3.3, p.17 (PDF p.19): "Fix a subspace V, let p = Q(𝔽ⁿ₂ \ V),
and let 0 < q, η < 1. There is a finite-bit test that uses N_g = ⌈512/(qη²)⌉ fresh samples and
outputs “continue” or “skip” with the following properties. (i) Two runs on independent samples with
a shared seed disagree with probability at most η. (ii) If p > q, the test skips with probability at
most η. (iii) If p < q/4, the test continues with probability at most η."

The test is `gate q η V` of the proof (threshold `θ` with shared uniform `J ∈ {0, …, B−1}`), run on
`N_g` samples `S ∼ Q^{N_g}`; `true` is "continue". -/
theorem lemma_3_3 (n : ℕ) (Q : PMF (Vec n)) (V : Subsp n) (q η : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    prIID2 Q (gateN q η) (fun S S' (J : Fin (gateB η)) => gate q η V S J ≠ gate q η V S' J) ≤ η ∧
    (q < massOutside Q V →
      prIID Q (gateN q η) (fun S (J : Fin (gateB η)) => gate q η V S J = false) ≤ η) ∧
    (massOutside Q V < q / 4 →
      prIID Q (gateN q η) (fun S (J : Fin (gateB η)) => gate q η V S J = true) ≤ η) := by sorry

end ReplParity
