-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_level_order_is_eichler
-- name    : RamanujanLiftTower136.Tower.level_order_is_eichler
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T12:49:57.956188+00:00
-- url     : https://prove2.me/theorems/c226e9e7-27b4-47eb-a901-4ffd00e4f874
-- title:
--   Section 3.5 — $E_n$ is an Eichler order of level $Q^{n+2}$
-- statement:
--   Throughout, $F=\mathbb Q(\sqrt{17})$ with ring of integers $\mathcal O_F$, $D=\left(\frac{-1,-3}{F}\right)$ is the fixed totally definite quaternion algebra, $\mathcal O\subset D$ is the fixed maximal order of equation (3.7), and $Q=(2,\omega)$, $\omega=\frac{1+\sqrt{17}}2$, is the fixed prime ideal above $2$. Let $\psi:D_Q\to M_2(\mathbb Q_2)$ be the fixed splitting of equation (3.8).
--
--   For $n\ge0$ let $E_n\subset\mathcal O$ be the order of equation (3.9): the elements $x\in\mathcal O$ whose matrix $\psi(x)$ has upper-right entry divisible by $2^{n+1}$ and lower-left entry divisible by $2$. Then
--   $$E_n\ \text{is an Eichler order of level}\ Q^{\,n+2}.$$
--
--   Explicitly:
--
--   1. $E_n$ is an $\mathcal O_F$-order in $D$ and is the intersection of two maximal orders;
--   2. at the prime $Q$ there is an isomorphism $D_Q\simeq M_2(F_Q)$ carrying the completion $(E_n)_Q$ onto the standard order $\begin{pmatrix}\mathcal O_{F,Q}&\mathcal O_{F,Q}\\2^{n+2}\mathcal O_{F,Q}&\mathcal O_{F,Q}\end{pmatrix}$;
--   3. at every prime $R\ne Q$ the completion $(E_n)_R$ is conjugate to $\mathcal O_R$.
--
--   This is the hypothesis under which Proposition 3.3 (scalar units, class count) and the automorphic spectral input of Section 5 apply to the level orders of the tower; the shift by two is part of the fixed choice of base order.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects → the shared concrete definitions over the quadratic algebra; reason: the representations preserve the field, the orders and all source instances
--   - encoding: "Eichler order of global level $Q^{n+2}$" → the three explicit clauses above (the shared predicate for Eichler orders of level $Q^m$, with $m=n+2$); reason: this is the mission's definition of the notion, already used as a hypothesis in Proposition 3.3
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.12 (PDF p.13), Section 3.5, equation (3.9) and the sentence "Consequently E_n is an Eichler order of global level Q^{n+2}". https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals

namespace RamanujanLiftTower136.Tower

theorem level_order_is_eichler (n : ℕ) : eichlerLevel (levelOrder n) (n+2) := by sorry

end RamanujanLiftTower136.Tower
