-- Prove2me | Theorems.Thm_QMAvsQCMAH_lemma_11
-- name    : QMAvsQCMAH.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:52.457896+00:00
-- url     : https://prove2.me/theorems/ddd10cf0-60b2-459f-acd1-833a61aca52d
-- title:
--   Lemma 11 — Kelley's switching lemma for sparse random restrictions
-- statement:
--   Let $w,h\ge1$ be integers, let $F$ be a width-$w$ DNF on a finite set $\mathcal Y$, and let $0<p\le1/(16w)$. Suppose a random set $P'\subseteq\mathcal Y$ satisfies $\Pr_{P'}[S\subseteq P']\le p^{|S|}$ for all $S\subseteq\mathcal Y$ with $|S|\le w+h$. Independently sample $B'\leftarrow\mathrm{Bernoulli}(1/2)^{\mathcal Y}$ and put $U'=B'|_{\mathcal Y\setminus P'}$. Then
--   $$\Pr_{P',B'}\bigl[\mathrm{DT}(g^{P',U'})\ge h\bigr]\le2(8wp)^h,$$
--   where $g^{P',U'}$ is the restriction of $F$ and $\mathrm{DT}$ is deterministic decision-tree depth.
--
--   Differences from the source:
--   - generalization: a finite set Y ⊆ {0,1}* → any finite type Y; reason: a finite subset of {0,1}* is such a type
--   - reading: a width-w DNF → a DNF of width at most w; reason: the standard meaning of width-w
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 11, p.38 (PDF p.41)

import Definitions.Def_QMAvsQCMAH_DNF
import Definitions.Def_QMAvsQCMAH_DTdepth
import Definitions.Def_QMAvsQCMAH_restrictFn
import Definitions.Def_QMAvsQCMAH_prob

set_option autoImplicit false

namespace QMAvsQCMAH

/-- **Lemma 11 (Kelley's switching lemma).** Let `w, h ≥ 1`, let `F` be a width-`w` DNF on a
finite set `Y`, and let `0 < p ≤ 1/(16w)`. Suppose a random set `P′ ⊆ Y` satisfies
`Pr[S ⊆ P′] ≤ p^{|S|}` for every `S ⊆ Y` with `|S| ≤ w + h`. Independently sample
`B′ ← Bernoulli(1/2)^Y` and put `U′ = B′|_{Y∖P′}`. Then
`Pr_{P′,B′}[DT(g^{P′,U′}) ≥ h] ≤ 2(8wp)^h`, where `g^{P′,U′}` is the restriction of `F`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 11, p.38 (PDF p.41): "Let w, h ≥ 1 be integers, let F be a width-w DNF on a finite set
Y ⊆ {0, 1}∗, and let 0 < p ≤ 1/(16w). Suppose a random set P′ ⊆ Y satisfies Pr_{P′}[S ⊆ P′] ≤
p^{|S|} (S ⊆ Y, |S| ≤ w + h). Independently sample B′ ← Bernoulli(1/2)^Y and put U′ = B′|_{Y\P′}.
Then Pr_{P′,B′}[DT(g^{P′,U′}) ≥ h] ≤ 2(8wp)^h, where g^{P′,U′} is the restriction of F
(Definition 23) and DT denotes deterministic decision-tree depth."

**Formalization Note.** "Width-`w`" is width at most `w`. Uniform `B′` has weight `2^{−|Y|}`. -/
theorem lemma_11 {Y : Type} [Fintype Y] [DecidableEq Y] (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) (F : DNF Y) (hF : DNF.width F ≤ w) (p : ℝ) (hp : 0 < p) (hp' : p ≤ 1 / (16 * w)) (μ : Finset Y → ℝ) (hμ : IsDist μ) (hinc : ∀ S : Finset Y, S.card ≤ w + h → prob μ (fun P => S ⊆ P) ≤ p ^ S.card) : ∑ P : Finset Y, ∑ B : Y → Bool, μ P * ((2 : ℝ) ^ Fintype.card Y)⁻¹ * (if h ≤ DTdepth P (restrictFn (fun O => DNF.eval F O) P (offP B P)) then 1 else 0) ≤ 2 * (8 * w * p) ^ h := by sorry

end QMAvsQCMAH
