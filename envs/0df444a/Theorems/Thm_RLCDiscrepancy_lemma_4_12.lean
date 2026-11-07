-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_12
-- name    : RLCDiscrepancy.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:16.282239+00:00
-- url     : https://prove2.me/theorems/1f40b45a-3037-44f6-969e-a68fcf1ddce9
-- title:
--   Lemma 4.12 — $F_f$ controls the one-step change of $\delta_{C,f}$
-- statement:
--   Let $f:\mathbb F_q^n\to\mathbb R_{\ge0}$ be normalized and let $C\subseteq\mathbb F_q^n$ be a linear code with $\delta_{C,f}\ne0$. Let $u$ be uniform in $\mathbb F_q^n$ and $C'=C+\operatorname{span}(u)$. Then for every $\lambda>0$,
--
--   $$
--   \Pr_u\Big[|\delta_{C',f}|>|\delta_{C,f}|\Big(\frac1q+\lambda\Big)\Big]\le\Big(\frac{q-1}{q}\Big)^2\frac{\delta_{C,F_f}}{\lambda^2\,\delta_{C,f}^2}.
--   $$
--
--   Adding one random generator shrinks the deviation by a factor about $1/q$ in expectation; the lemma bounds the probability of falling short of that by more than $\lambda|\delta_{C,f}|$ in terms of the deviation of the self-convolution.
--
--   **Formalization Note** $\lambda$ is named `lam`.
--
--   Differences from the source:
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
--   - encoding: Pr over a uniform random object → the counting ratio `PunctSketch.coinProb` over all outcomes; reason: the paper's law is uniform on a finite space; same values
--   - encoding: C′ = C + span(u) → `C ⊔ Submodule.span F {u}`; reason: the same subspace
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.12, p.30

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_PunctSketch_coinProb

namespace RLCDiscrepancy

/-- **Lemma 4.12** (deviation of F_f controls the change in deviation of f). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.12,
p.30: "Let f : F^n_q → R≥0 be normalized. Fix a linear code C ⊆ F^n_q and assume δ_{C,f} ≠ 0. Let
u ∼ F^n_q be a uniformly random vector, and let C′ = C + span(u). Then, for any λ > 0:
Pr_u[|δ_{C′,f}| > |δ_{C,f}| (1/q + λ)] ≤ ((q−1)/q)² δ_{C,F_f} / (λ² · δ²_{C,f})."

**Formalization Note.** λ is `lam` (λ is reserved in Lean). The probability is the fraction of
the q^n vectors `u` with the (strict) event; C + span(u) is `C ⊔ span {u}`. -/
theorem lemma_4_12 {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ)
    (hf : IsNormalized f) (C : Submodule F (Fin n → F)) (hδ : relDev C f ≠ 0) (lam : ℝ)
    (hlam : 0 < lam) :
    PunctSketch.coinProb (fun u : Fin n → F =>
        |relDev C f| * (1 / (Fintype.card F : ℝ) + lam) <
          |relDev (C ⊔ Submodule.span F {u}) f|) ≤
      (((Fintype.card F : ℝ) - 1) / Fintype.card F) ^ 2 * relDev C (selfConv f) /
        (lam ^ 2 * relDev C f ^ 2) := by sorry

end RLCDiscrepancy
