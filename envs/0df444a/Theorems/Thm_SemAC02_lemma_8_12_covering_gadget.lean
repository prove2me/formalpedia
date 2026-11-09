-- Prove2me | Theorems.Thm_SemAC02_lemma_8_12_covering_gadget
-- name    : SemAC02.lemma_8_12_covering_gadget
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:03.878495+00:00
-- url     : https://prove2.me/theorems/bd34dffa-01ad-46fc-9810-c35bc76665ba
-- title:
--   Lemma 8.12 — a one-sided covering gadget
-- statement:
--   Fix $d\ge2$. For all sufficiently small $\epsilon>0$, put $L=\epsilon^{-1/(d-1)}$ and let $m$ be the smallest odd integer at least $128L^{2d-1}$. There is a monotone, alternating, OR-rooted AND/OR formula $C_m$ of depth at most $d+1$ and size $\exp(O_d(L))$ such that
--   $$
--   |x|\ge m/2\ \Longrightarrow\ C_m(x)=1,\qquad \Pr_{X\sim\mathrm{Bern}(1/2-\epsilon)^m}[C_m(X)=1]\le e^{-L}.
--   $$
--   Every child of the OR root is AND-rooted and has depth at most $d$. In particular $m=\Theta_d(L^{2d-1})$.
--
--   Its complement $\neg C_m$ is the gadget of Lemma 8.7: it rejects every input of weight at least $m/2$ and accepts all but an $e^{-L}$ fraction of inputs of density $1/2-\epsilon$.
--
--   Differences from the source:
--   - encoding: O_d(L), Θ_d(L^{2d−1}), "for all sufficiently small ε > 0" → one constant A (and ε₀ > 0) chosen before ε; ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); reason: standard reading of O_d(·) and "for all sufficiently small ε"; the constants depend on d only
--   - encoding: m the smallest odd integer at least 128L^{2d−1} → hypotheses Odd m, 128L^{2d−1} ≤ m, and m ≤ m' for every odd m' ≥ 128L^{2d−1}; reason: these characterise the smallest such odd integer
--   - encoding: alternating, OR-rooted formula whose root children are AND-rooted → IsReduced (no gate has a child of its own type, no repeated children), root `or cs`, every c ∈ cs an AND gate, size = treeSize; reason: the paper's circuit conventions of p.17; for a formula the size is its number of nodes
--   - encoding: Pr over Bern(p)^m → bernProb p, the explicit finite sum; reason: same numbers
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.12, p.67 (PDF p.69)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb

namespace SemAC02

/-- **Lemma 8.12 (A one-sided covering gadget)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.12, p.67): fix
`d ≥ 2`. For all sufficiently small `ϵ > 0`, put `L = ϵ^{−1/(d−1)}` and let `m` be the smallest
odd integer at least `128 L^{2d−1}`. There exists a monotone, alternating, OR-rooted AND/OR
formula `C_m` of depth at most `d + 1` and size `exp(O_d(L))` such that
`|x| ≥ m/2 ⟹ C_m(x) = 1` and `Pr_{X∼Bern(1/2−ϵ)^m}[C_m(X) = 1] ≤ e^{−L}`.
Every child of the OR root is AND-rooted and has depth at most `d`. In particular,
`m = Θ_d(L^{2d−1})`.

**Formalization Note** `O_d`, `Θ_d`: constants `A`, `B₁ > 0`, `B₂` chosen before `ϵ`.
"Smallest odd integer at least `x`" is stated by the three hypotheses on `m`. "Alternating" (no
gate has a child of its own type) is part of `IsReduced`, the paper's normal form; size is tree
size. -/
theorem lemma_8_12_covering_gadget (d : ℕ) (hd : 2 ≤ d) :
    ∃ A B₁ B₂ ε₀ : ℝ, 0 < B₁ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ m : ℕ, Odd m →
      128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m : ℝ) →
      (∀ m' : ℕ, Odd m' → 128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m' : ℝ) → m ≤ m') →
      ∃ Cm : Circ (Fin m), IsMonotoneCirc Cm ∧ IsReduced Cm ∧ Cm.depth ≤ d + 1 ∧
        (Cm.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        (∃ cs, Cm = Circ.or cs ∧ ∀ c ∈ cs, c.isAnd = true ∧ c.depth ≤ d) ∧
        (∀ x : Fin m → Bool, (m : ℝ) / 2 ≤ (hammingWeight x : ℝ) → Cm.eval x = true) ∧
        bernProb (1 / 2 - ε) (fun x => Cm.eval x) ≤ Real.exp (-(ε ^ (-1 / ((d : ℝ) - 1)))) ∧
        B₁ * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ B₂ * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) := by sorry

end SemAC02
