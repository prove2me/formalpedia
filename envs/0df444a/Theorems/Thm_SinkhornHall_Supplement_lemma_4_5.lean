-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_4_5
-- name    : SinkhornHall.Supplement.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:11:35.012396+00:00
-- url     : https://prove2.me/theorems/0ffa5017-7f4a-487f-a2b6-1de58356ae6f
-- title:
--   Lemma 4.5 — $D(N^*\|M_0)\le 2n\log(nA_{\max}/A_{\min})$
-- statement:
--   Setting of §4: $A$ is a nonnegative $n\times n$ matrix with no zero row or column (its support graph $G=G(A)$ has no isolated node), the marginals are $(r,c)=(\mathbf 1,\mathbf 1)$, $A_{\max}$ is the largest entry and $A_{\min}$ the least positive entry of $A$, and $(M_k,N_k)$ is the Sinkhorn sequence $N_0=C(A)$, $M_k=R(N_k)$, $N_{k+1}=C(M_k)$. Let $N^*$ be the limit of $N_k$, and $M_0=R(C(A))$. Then
--
--   $$D(N^*\|M_0)\le 2n\log\frac{nA_{\max}}{A_{\min}}.$$
--
--   With Lemma 2.13 ($C=R=n$) this bounds the distance of the row marginals of $N_\ell$ from $p^*$, giving the iteration count of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $M_{ij}=0<N_{ij}$; reason: the paper's $\infty$ convention, same instances
--   - encoding: the Sinkhorn limit $(M^*,N^*)$ (the limit of $(M_k,N_k)$, Theorem 2.10) → a hypothesis that $(M_k,N_k)$ (or $N_k$) converges to the given matrices; reason: the paper defines the limit through Theorem 2.10, which the mission states separately; for the actual limit the statements coincide
--   - encoding: $\log$ → `Real.log` (natural logarithm); reason: the paper's $\log$
--   - encoding: $[n]$ with $n=|U|=|V|$ → `Fin n` with any `n : ℕ`; reason: 0-based relabelling; for $n=0$ the statement is trivially true
--   - generalization: stated inside the proof of Theorem 4.3, under its hypothesis "$G$ has no perfect matching" (p.16) → that hypothesis is not assumed; reason: the lemma's proof (p.17) never uses it; with the hypothesis added it is the source's claim
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 4.5, p.17

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 4.5.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 4.5, p.17: "D(N*‖M_0) ≤ 2n log nA_max/A_min."

Setting of §4 (p.15): `A` is a nonnegative `n × n` matrix with no zero row or column (no isolated
node of `G = G(A)`), `(r, c) = (1, 1)`, `A_max` its largest entry and `A_min` its least positive
entry; `M_0 = R(C(A))` and `N*` is the limit of the Sinkhorn sequence (2.6).

**Formalization Note.** `N*` enters as a hypothesis `N_k → N*` (Theorem 2.10). `D` is `matKL` in
`EReal`; `log` is `Real.log` (natural). -/
theorem lemma_4_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (Nstar : Matrix (Fin n) (Fin n) ℝ) (hN : Tendsto (sinkhornN A 1 1) atTop (𝓝 Nstar)) :
    matKL Nstar (sinkhornM A 1 1 0) ≤
      ((2 * (n : ℝ) * Real.log ((n : ℝ) * SinkhornHall.Amax A / SinkhornHall.Amin A) : ℝ) :
        EReal) := by sorry

end SinkhornHall.Supplement
