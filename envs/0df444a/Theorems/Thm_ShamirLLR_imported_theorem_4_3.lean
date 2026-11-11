-- Prove2me | Theorems.Thm_ShamirLLR_imported_theorem_4_3
-- name    : ShamirLLR.imported_theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:21.230232+00:00
-- url     : https://prove2.me/theorems/640fd67f-8ad5-40f1-80a0-74ecb33d5d0b
-- title:
--   Imported Theorem 4.3 — periodic arithmetic regularity
-- statement:
--   Fix $\varepsilon>0$ and a growth function $F:\mathbb R_{>0}\to\mathbb R_{>0}$. There is $M_0=M_0(\varepsilon,F)$ such that for every odd prime $p$ and every $f:\mathbb F_p\to[0,1]$ there are a number $0<M_f<M_0$ and a decomposition
--   $$
--   f=f_{\mathrm{nil}}+f_{\mathrm{sml}}+f_{\mathrm{unf}},\qquad \|f_{\mathrm{sml}}\|_2\le\varepsilon,\qquad \|f_{\mathrm{unf}}\|_{U^3}\le 1/F(M_f),
--   $$
--   where $f_{\mathrm{nil}}$ takes values in $[0,1]$ and is a $p$-periodic polynomial nilsequence of degree at most two and complexity at most $M_f$: $f_{\mathrm{nil}}(\bar z)=F_0(g(z)\Gamma)$ for a degree-two filtered nilmanifold $G/\Gamma$ of dimension at most $M_f$ whose filtration degree and structure-constant heights are at most $M_f$, a quadratic orbit $g$ that is $p$-periodic modulo $\Gamma$, and a readout $F_0:G/\Gamma\to\mathbb C$ with $\|F_0\|_{\mathrm{Lip}}\le M_f$. The bound $M_0$ is independent of $p$ and $f$.
--
--   This is the literature input (Candela–Sisask) from which the smooth class is built.
--
--   Differences from the source:
--   - reading: "complexity at most $M_f$" → $d_G\le M_f$, filtration degree $2\le M_f$, `G.complexity` (largest structure-constant height) $\le M_f$, and $\|F_0\|_{\mathrm{Lip}}\le M_f$; reason: the convention of §3.1, p.19: complexity bounds $d_G$, the filtration degree, the rationality of the basis and the readout's Lipschitz norm
--   - reading: $f_{\mathrm{sml}}, f_{\mathrm{unf}}$ of unstated type → real-valued $f_{\mathrm{sml}}, f_{\mathrm{unf}}$; reason: the stronger reading; equivalent, since $f-f_{\mathrm{nil}}$ is real and taking real parts does not increase $\|\cdot\|_2$ or $\|\cdot\|_{U^3}$
--   - encoding: a $p$-periodic polynomial nilsequence of degree at most two → $f_{\mathrm{nil}}(z)=F_0(g(z))$ for all $z\in\mathbb Z$ with $G$ an `LSS.Nilmanifold 2`, $g$ in Taylor form and $p$-periodic modulo $\Gamma$, $F_0$ right-$\Gamma$-invariant; reason: definitions of §3.1–3.2; every degree-two filtered nilmanifold with adapted Mal'cev basis is basis-preservingly isomorphic to such a matrix realization
--   - encoding: growth function $F:\mathbb R_{>0}\to\mathbb R_{>0}$ → $F:\mathbb R\to\mathbb R$ positive on $(0,\infty)$; reason: only values at positive arguments enter
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Imported Theorem 4.3, p.27 (PDF p.28) [CS14, Theorem 3.4]; complexity convention §3.1, p.19

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_nilCoords
import Definitions.Def_ShamirLLR_nilSmooth
import Definitions.Def_ShamirLLR_gowersU3

set_option autoImplicit false

namespace ShamirLLR

/-- **Imported Theorem 4.3 (Periodic arithmetic regularity; [CS14, Theorem 3.4]).** Fix `ε > 0`
and a growth function `F : ℝ_{>0} → ℝ_{>0}`. There is `M₀ = M₀(ε, F)` such that for every odd
prime `p` and every `f : 𝔽_p → [0, 1]` there are `0 < M_f < M₀` and a decomposition
`f = f_nil + f_sml + f_unf` with `‖f_sml‖₂ ≤ ε`, `‖f_unf‖_{U³} ≤ 1/F(M_f)`, where `f_nil` is a
`p`-periodic polynomial nilsequence of degree at most two and complexity at most `M_f`, taking
values in `[0, 1]`. `M₀` is independent of `p` and `f`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Imported Theorem 4.3, p.27; complexity convention §3.1, p.19 ("Complexity at most M bounds d_G,
the filtration degree, and the rationality of the basis; for a nilsequence, it also bounds the
Lipschitz norm of its readout"); periodic nilsequences §3.2, p.19.

**Formalization Note.** `f_nil(z̄) = F₀(g(z)Γ)` for every integer `z`, with `G` an
`LSS.Nilmanifold 2` (degree-two filtration, adapted Mal'cev basis), `g` in Taylor form and
`p`-periodic modulo `Γ`, and `F₀ : G/Γ → ℂ` Lipschitz. Complexity at most `M_f`: `d_G ≤ M_f`,
filtration degree `2 ≤ M_f`, structure-constant heights `≤ M_f` (`G.complexity`), and
`‖F₀‖_{Lip} ≤ M_f`. `f_sml` and `f_unf` are real-valued. The growth function is a real function
positive on `(0, ∞)`. -/
theorem imported_theorem_4_3 (ε : ℝ) (hε : 0 < ε) (F : ℝ → ℝ) (hF : ∀ t, 0 < t → 0 < F t) :
    ∃ M₀ : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ f : ZMod p → ℝ, (∀ z, 0 ≤ f z ∧ f z ≤ 1) →
      ∃ Mf : ℝ, 0 < Mf ∧ Mf < M₀ ∧ ∃ fnil fsml funf : ZMod p → ℝ,
        f = fnil + fsml + funf ∧ l2norm (fun z => (fsml z : ℂ)) ≤ ε ∧
        gowersU3 (fun z => (funf z : ℂ)) ≤ 1 / F Mf ∧ (∀ z, 0 ≤ fnil z ∧ fnil z ≤ 1) ∧
        ∃ G : LSS.Nilmanifold 2, (G.d : ℝ) ≤ Mf ∧ (2 : ℝ) ≤ Mf ∧ G.complexity ≤ Mf ∧
          ∃ g : ℤ → G.Mat, IsQuadPoly G g ∧ IsPPeriodic G p g ∧
            ∃ F₀ : G.Mat → ℂ, LipNormLE G F₀ Mf ∧ ∀ z : ℤ, ((fnil (z : ZMod p) : ℝ) : ℂ) = F₀ (g z) := by sorry

end ShamirLLR
