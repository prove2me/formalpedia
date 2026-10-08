-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_oracle_valid
-- name    : PrivLearn.MaskedParity.oracle_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:33.356159+00:00
-- url     : https://prove2.me/theorems/032cd8f6-f1ed-4f49-b774-1c1908d9933a
-- title:
--   Proof of Theorem 5.16(2), pp. 30–31 — 𝒪 is a valid SQ oracle and answers independently of ā when |⟨f⁰_g, c⁰⟩| < τ
-- statement:
--   Let examples be uniform on the MASKED-PARITY domain $D$ and let $\mathcal O$ be the SQ oracle of §5.3.2.
--
--   1. $\mathcal O$ is a valid SQ oracle: for every target $c_{r,a}$, every real-valued query $g$ and every tolerance $\tau>0$,
--   $$\bigl|\mathcal O_{c_{r,a},\mathcal D}(g,\tau)-\mathbb E[g(u,c_{r,a}(u))]\bigr|\le\tau .$$
--   2. If $|\langle f^0_g,c^0_{r,0}\rangle|<\tau$, then $\mathcal O$ gives the same answer to $(g,\tau)$ on the targets $c_{r,0}$ and $c_{r,1}$:
--   $$\mathcal O_{c_{r,0},\mathcal D}(g,\tau)=\mathcal O_{c_{r,1},\mathcal D}(g,\tau).$$
--
--   Together these make $\mathcal O$ a legal oracle that, on queries with small correlation with the $b=0$ half of the target, can be simulated from $r$ without knowledge of $a$.
--
--   **Formalization Note.** The paper states the validity in passing ("there is a valid SQ oracle which, conditioned on Good, can be simulated using $\bar r$ but without knowledge of $\bar a$"); this item makes both parts explicit. The paper's tolerances lie in $(0,1)$; validity is stated for every $\tau>0$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, pp. 30–31, proof of Theorem 5.16 part (2), the oracle O and the paragraph after Pr[Good]

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **The oracle `𝒪` is a valid SQ oracle that does not reveal `ā` on small correlations**
(proof of Theorem 5.16(2), pp. 30–31). For every target `c_{r,a}`, every real-valued query `g` and
every tolerance `τ > 0`, the answer `𝒪(g, τ)` is within `τ` of `E[g(u, c_{r,a}(u))]`; and whenever
`|⟨f^0_g, c^0_{r,0}⟩| < τ`, the oracle gives the same answer on `c_{r,0}` and on `c_{r,1}`. -/
theorem oracle_valid {d : ℕ} :
    (∀ (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ), 0 < τ →
      IsLabeledSQAnswer (cMP r a) g τ (oracleO r a g τ)) ∧
    (∀ (r : Fin d → ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ),
      |ip (half 0 (fg g)) (half 0 (cMP r 0))| < τ → oracleO r 0 g τ = oracleO r 1 g τ) := by sorry

end PrivLearn.MaskedParity
