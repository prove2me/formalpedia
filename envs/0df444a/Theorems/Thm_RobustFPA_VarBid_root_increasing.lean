-- Prove2me | Theorems.Thm_RobustFPA_VarBid_root_increasing
-- name    : RobustFPA.VarBid.root_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:38.486102+00:00
-- url     : https://prove2.me/theorems/560706ce-15f3-49f3-85f3-fe0b69078472
-- title:
--   Proof of Proposition 4, p. 51 — the root of Equation (3) strictly increases from $n$ to $n+1$ bidders
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$ and $L < v$. Write $u^+_n$, $u^-_n$, $\tilde b_n$ for the functions of the ClosedForms file with $n$ bidders. If $b$ solves Equation (3) for $n$ bidders on $[\max\{L,\tilde b_n\}, v]$,
--   $$
--   u^+_n(\max\{L,\tilde b_n\}) - u^+_n(b) = u^+_n(b) - u^-_n(b),
--   $$
--   and $b'$ solves Equation (3) for $n+1$ bidders on $[\max\{L,\tilde b_{n+1}\}, v]$, then
--   $$
--   b < b'.
--   $$
--
--   This is the comparative statics part of Proposition 4: the minimax loss bid shades less as competition grows.
--
--   **Formalization Note.** The paper differentiates the root $E(b,n) = 0$ in a real-valued $n$ via the implicit function theorem; the statement here is the integer comparison between $n$ and $n+1$ bidders, which is what "increases in the number of bidders" means. The increase is strict, as in the paper's $\partial E/\partial n < 0$. Same $\tau$, $L$, $v$ for both $n$ and $n+1$.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 51 (Appendix B.4, proof of Proposition 4: the minimax loss bid increases in n)

import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem root_increasing (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (b b' : ℝ)
    (hb : peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)
    (hb' : peakBid (n + 1) τ L v ≤ b' ∧ b' ≤ v ∧ Equation3 (n + 1) τ L v b') :
    b < b' := by sorry

end RobustFPA.VarBid
