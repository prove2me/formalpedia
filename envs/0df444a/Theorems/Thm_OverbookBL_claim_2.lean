-- Prove2me | Theorems.Thm_OverbookBL_claim_2
-- name    : OverbookBL.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:17.887591+00:00
-- url     : https://prove2.me/theorems/9a178c56-5394-4498-ad43-74e0f60f62ce
-- title:
--   Claim 2 — replacing $X_{i,x_i+1}$ by $X_{i,x_i}+1$ in an overflow probability
-- statement:
--   Let $\vec x$ be an acceptance vector, $i\ne j$ two types and $d$ a natural number with $x_j\ge d+1$. Then
--
--   $$
--   \mathbb P\Big[\sum_{n\ne i,j}X_{n,x_n}+X_{j,x_j-d-1}\ge B-X_{i,x_i+1}\Big]\le\mathbb P\Big[\sum_{n\ne i,j}X_{n,x_n}+X_{j,x_j-d-1}\ge B-1-X_{i,x_i}\Big],
--   $$
--
--   with independent $X_{n,y}\sim\mathrm{Bin}(y,p_n)$. The paper states it for $d=\delta_j$ and for $\vec x$ such that $\vec x-(\delta_j+1)e_j+e_i$ is feasible for (1).
--
--   An extra type-$i$ customer shows up at most once, so it can raise the show-up count by at most one; Claim 2 records this in the form used in the proof of Lemma 2.
--
--   Differences from the source:
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - generalization: d = δⱼ (the constant of the proof of Lemma 2) → any natural number d with d + 1 ≤ xⱼ; reason: the inequality holds for every d; specializes to d = δⱼ
--   - generalization: x⃗ − (δⱼ+1)eⱼ + eᵢ feasible for (1) → only xⱼ ≥ d + 1; reason: the caps of (1) play no role; feasibility implies xⱼ ≥ δⱼ + 1
--   - encoding: events Σ … ≥ B − X_{i,xᵢ+1} and Σ … ≥ B − 1 − X_{i,xᵢ} → show-up count of x − (d+1)eⱼ + eᵢ is ≥ B, and show-up count of x − (d+1)eⱼ plus one is ≥ B; reason: the Xᵢ terms moved across ≥ to avoid ℕ subtraction; i ≠ j is implicit in "n ≠ i, j"
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Claim 2, p.17 (proof Appendix A.2, pp.42–43)

import Definitions.Def_OverbookBL_Instance
import Definitions.Def_OverbookBL_showE

namespace OverbookBL

/-- **Claim 2** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.17). Let
`x` be an acceptance vector, `i ≠ j` two types and `d` a natural number with `xⱼ ≥ d + 1`. Then
`P[∑_{n≠i,j} X_{n,xₙ} + X_{j,xⱼ−d−1} ≥ B − X_{i,xᵢ+1}] ≤ P[∑_{n≠i,j} X_{n,xₙ} + X_{j,xⱼ−d−1} ≥ B − 1 − X_{i,xᵢ}]`.

**Formalization Note** With `w = x − (d+1)eⱼ`, the left event is "the show-up count of `w + eᵢ`
is `≥ B`" and the right event is "the show-up count of `w`, plus one, is `≥ B`"; the `Xᵢ` terms are
moved to the left of `≥` to avoid `ℕ` subtraction. The paper states the claim for `d = δⱼ` and for
`x` such that `x − (δⱼ+1)eⱼ + eᵢ` is feasible for (1); here `d` and `x` are arbitrary (with
`xⱼ ≥ d + 1`). -/
theorem claim_2 {k : ℕ} (I : Instance k) (B : ℕ) (x : Fin k → ℕ) (i j : Fin k) (d : ℕ) (hij : i ≠ j) (hx : d + 1 ≤ x j) : tailProb I.p B (x - (d + 1) • Pi.single j 1 + Pi.single i 1) ≤ showE I.p (x - (d + 1) • Pi.single j 1) (fun s => if B ≤ s + 1 then 1 else 0) := by sorry

end OverbookBL
