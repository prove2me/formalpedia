-- Prove2me | Theorems.Thm_SysBathGibbs_lemma_4_2
-- name    : SysBathGibbs.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:18.776195+00:00
-- url     : https://prove2.me/theorems/9f1d4b2c-9e85-4392-a72f-2f1f1ba48d82
-- title:
--   Lemma 4.2 — Complex-time locality
-- statement:
--   Let $H_n$ be a chain as in (1.2), $x\in[n]$, and $\mathcal E_{x,r}$ the normalized partial trace onto $N_r(x)$.
--
--   1. (Strictly local matrices at complex times.) For every $d\ge0$ and $u_*\ge0$ there are $C,c>0$ and $v\ge0$, depending only on $d$ and $u_*$, such that for every operator $B_x$ supported on $N_d(x)$, all $t\in\mathbb R$, $r\ge0$ and $|u|\le u_*$,
--   $$
--   \|B_x(t-iu)\|_{\mathrm{op}}\le C\|B_x\|_{\mathrm{op}},\qquad \|(\mathrm{id}-\mathcal E_{x,r})B_x(t-iu)\|_{\mathrm{op}}\le C\|B_x\|_{\mathrm{op}}\min\{1,e^{v|t|-cr}\},
--   $$
--   and, at $t=0$, $\|(\mathrm{id}-\mathcal E_{x,r})B_x(-iu)\|_{\mathrm{op}}\le C'e^{-c'r\log(r+1)}\|B_x\|_{\mathrm{op}}$ with constants $C',c'>0$ depending only on $d,u_*$.
--   2. (Quasi-local matrices at real times.) For every $\mu>0$ there are $C_\mu,c_\mu>0$ and $v_\mu\ge0$ depending only on $\mu$ such that, if $\|D_x\|_{\mathrm{op}}\le M$ and $\|(\mathrm{id}-\mathcal E_{x,r})D_x\|_{\mathrm{op}}\le Me^{-\mu r}$ for all $r\ge0$, then for all $t\in\mathbb R$, $r\ge0$, with $D_x(t)=e^{itH_n}D_xe^{-itH_n}$,
--   $$
--   \|D_x(t)\|_{\mathrm{op}}=\|D_x\|_{\mathrm{op}},\qquad \|(\mathrm{id}-\mathcal E_{x,r})D_x(t)\|_{\mathrm{op}}\le C_\mu M\min\{1,e^{v_\mu|t|-c_\mu r}\}.
--   $$
--
--   Here $B(z)=e^{izH_n}Be^{-izH_n}$. The lemma is the source of all locality estimates of the paper.
--
--   Differences from the source:
--   - reading: "the constants only depend on d and u∗" / "only depend on µ" → the constants are chosen before q, n, the chain, x; reason: the page's literal dependence; the stronger reading is taken (no dependence on q)
--   - reading: "the second bound can be replaced by Ce^{−cr log(r+1)}‖B_x‖_op" at t = 0 → its own constants C′, c′ > 0, depending only on d, u∗; reason: the page does not say the same C, c serve; separate constants are the literal content
--   - encoding: ‖D_x(t)‖_op = ‖D_x‖_op ≤ M → the equality only; ≤ M is the hypothesis; reason: the inequality is the hypothesis (4.6) restated
--   - encoding: a chain [n] of qudits of dimension 2^q → q ≥ 1 as a hypothesis; reason: a qudit has q ≥ 1 qubits
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Lemma 4.2 (eqs. (4.5)–(4.7)), p.31

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Lemma 4.2 (Complex-time locality)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.31.
(i) For `supp B_x ⊆ N_d(x)`, `t ∈ ℝ`, `r ≥ 0`, `|u| ≤ u⋆`: `‖B_x(t-iu)‖_op ≤ C‖B_x‖_op` and
`‖(id - E_{x,r}) B_x(t-iu)‖_op ≤ C‖B_x‖_op min{1, e^{v|t|-cr}}`; at `t = 0` the second bound can be
replaced by `C e^{-cr log(r+1)} ‖B_x‖_op`. The constants depend only on `d` and `u⋆`.
(ii) If `‖D_x‖_op ≤ M` and `‖(id - E_{x,r}) D_x‖_op ≤ M e^{-μr}` for `r ≥ 0`, then for all `t`, `r ≥ 0`,
`‖D_x(t)‖_op = ‖D_x‖_op ≤ M` and `‖(id - E_{x,r}) D_x(t)‖_op ≤ C_μ M min{1, e^{v_μ|t|-c_μ r}}`, with
constants depending only on `μ`.

**Formalization Note.** The constants come before `q`, `n`, the chain and the site, as the page's
"only depend on" says. The constants of the `t = 0` clause are named `C'`, `c'`. -/
theorem lemma_4_2 :
    (∀ d uStar : ℝ, 0 ≤ d → 0 ≤ uStar →
      ∃ C c v C' c' : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ v ∧ 0 < C' ∧ 0 < c' ∧
        ∀ (n q : ℕ), 1 ≤ q → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ (x : Fin n) (B : SysMat n q), SupportedOn (nbhd d {x}) B →
            ∀ (t r u : ℝ), 0 ≤ r → |u| ≤ uStar →
              opNorm (evo (chainHam h) ((t : ℂ) - Complex.I * u) B) ≤ C * opNorm B ∧
              opNorm (evo (chainHam h) ((t : ℂ) - Complex.I * u) B -
                  traceAt x r (evo (chainHam h) ((t : ℂ) - Complex.I * u) B)) ≤
                C * opNorm B * min 1 (Real.exp (v * |t| - c * r)) ∧
              opNorm (evo (chainHam h) (-(Complex.I * u)) B -
                  traceAt x r (evo (chainHam h) (-(Complex.I * u)) B)) ≤
                C' * Real.exp (-c' * r * Real.log (r + 1)) * opNorm B) ∧
    (∀ μ : ℝ, 0 < μ →
      ∃ Cμ cμ vμ : ℝ, 0 < Cμ ∧ 0 < cμ ∧ 0 ≤ vμ ∧
        ∀ (n q : ℕ), 1 ≤ q → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ (x : Fin n) (D : SysMat n q) (M : ℝ), 0 < M → opNorm D ≤ M →
            (∀ r : ℝ, 0 ≤ r → opNorm (D - traceAt x r D) ≤ M * Real.exp (-μ * r)) →
            ∀ (t r : ℝ), 0 ≤ r →
              opNorm (evo (chainHam h) t D) = opNorm D ∧
              opNorm (evo (chainHam h) t D - traceAt x r (evo (chainHam h) t D)) ≤
                Cμ * M * min 1 (Real.exp (vμ * |t| - cμ * r))) := by sorry

end SysBathGibbs
